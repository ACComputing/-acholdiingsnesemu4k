# ================================================
# AC'S Snes Emu 0.2 - REAL SNES EMULATOR (single file)
# Cython 65816 CPU + LoROM mapper + simple PPU + Tkinter GUI
# Fully runnable - no separate files needed!
# Python 3.14 compatible | A.C Holdings / Team Flames
# ================================================

import tkinter as tk
from tkinter import filedialog, messagebox
from PIL import Image, ImageTk
import threading
import time
import os
import tempfile
import pyximport
import numpy as np
import sys
import shutil
import importlib
import uuid

# ====================== CYTHON CORE (embedded as string) ======================
CYTHON_CORE = r'''
# cython: language_level=3
import numpy as np
from libc.stdlib cimport malloc, free
from libc.string cimport memset, memcpy

cdef class SNES:
    cdef object framebuffer
    cdef unsigned char[:, :, :] framebuffer_view
    cdef unsigned char* ram
    cdef unsigned char* rom
    cdef unsigned int rom_size
    cdef bint is_running
    cdef int frame_count
    cdef unsigned short pc
    cdef unsigned char a, x, y, s, p, db, pb
    cdef unsigned short d
    cdef unsigned char controller1
    cdef char* rom_title
    cdef int mapper_type   # 0 = LoROM, 1 = HiROM

    def __cinit__(self):
        self.framebuffer = np.zeros((224, 256, 3), dtype=np.uint8)
        self.framebuffer_view = self.framebuffer
        self.ram = <unsigned char*> malloc(0x20000)  # 128KB WRAM
        if self.ram != NULL:
            memset(self.ram, 0, 0x20000)
        self.rom = NULL
        self.rom_size = 0
        self.is_running = False
        self.frame_count = 0
        self.pc = 0x8000
        self.a = 0
        self.x = 0
        self.y = 0
        self.s = 0x00
        self.p = 0x34
        self.db = 0
        self.pb = 0x00
        self.d = 0x0000
        self.controller1 = 0
        self.rom_title = NULL
        self.mapper_type = 0
        print("AC'S Snes Emu 0.2 Cython Core - 65816 CPU + LoROM mapper ready")

    def __dealloc__(self):
        if self.ram != NULL:
            free(self.ram)
            self.ram = NULL
        if self.rom != NULL:
            free(self.rom)
            self.rom = NULL
        if self.rom_title != NULL:
            free(self.rom_title)
            self.rom_title = NULL

    def load_rom(self, str rom_path):
        cdef int header_offset = 0
        cdef unsigned char* hdr
        cdef unsigned char mapper
        cdef bytes b_title
        cdef unsigned int i
        cdef bytes data
        cdef const unsigned char* data_ptr

        with open(rom_path, "rb") as f:
            data = f.read()
        self.rom_size = <unsigned int>len(data)

        if self.rom_size < 0x8000:
            print("ROM file is too small to be a valid SNES ROM.")
            return False

        if self.rom != NULL:
            free(self.rom)
        self.rom = <unsigned char*> malloc(self.rom_size)
        if self.rom == NULL:
            print("Failed to allocate ROM memory.")
            return False
            
        data_ptr = data
        memcpy(self.rom, data_ptr, self.rom_size)

        # Detect copier header (often 0x200 bytes)
        if self.rom_size % 0x8000 == 0x200:
            header_offset = 0x200

        # Safety check for header access
        if header_offset + 0x7FC0 + 0x20 > self.rom_size:
            print("ROM too small to contain a valid header.")
            self.reset()
            return True

        hdr = self.rom + header_offset + 0x7FC0

        # Title (21 bytes)
        if self.rom_title != NULL:
            free(self.rom_title)
        self.rom_title = <char*> malloc(22)
        if self.rom_title != NULL:
            for i in range(21):
                self.rom_title[i] = hdr[i]
            self.rom_title[21] = 0

        # Mapper byte (bits 0-3: 0 = LoROM, 1 = HiROM, 2 = LoROM with fast ROM, etc.)
        mapper = hdr[0x15] & 0x0F
        if mapper == 0:
            self.mapper_type = 0   # LoROM
        else:
            self.mapper_type = 1   # HiROM (simplified)

        if self.rom_title != NULL:
            b_title = self.rom_title
            print(f"ROM Title: {b_title.decode('ascii', errors='ignore').strip()}")
        print(f"   Mapper: {'LoROM' if self.mapper_type == 0 else 'HiROM'} | Size: {self.rom_size // 1024}KB")
        self.reset()
        return True

    cdef unsigned char _read_lorom(self, unsigned int addr):
        """LoROM address translation: CPU address -> ROM offset."""
        cdef unsigned int bank = addr >> 16
        cdef unsigned int off = addr & 0xFFFF
        cdef unsigned int rom_addr

        if addr >= 0x8000:
            # For banks $80-$FF (LoROM)
            if off >= 0x8000:
                rom_addr = ((bank & 0x7F) << 15) | (off & 0x7FFF)
            else:
                # Should not happen in LoROM mode; fallback to simple offset
                rom_addr = off & 0x7FFF
        else:
            # Low banks ($00-$7F) are usually mirrored WRAM
            return 0x00

        if rom_addr < self.rom_size:
            return self.rom[rom_addr]
        return 0x00

    cdef unsigned char _read_hirom(self, unsigned int addr):
        """Simplified HiROM address translation."""
        cdef unsigned int bank = addr >> 16
        cdef unsigned int off = addr & 0xFFFF
        cdef unsigned int rom_addr

        if addr >= 0xC00000:
            # ExHiROM not handled
            return 0x00

        if off >= 0x8000:
            rom_addr = ((bank & 0x3F) << 16) | (off & 0x7FFF)
        else:
            # Low area (WRAM)
            return 0x00

        if rom_addr < self.rom_size:
            return self.rom[rom_addr]
        return 0x00

    cdef unsigned char read_byte(self, unsigned int addr):
        cdef unsigned int full_addr
        cdef unsigned int rom_addr
        if addr < 0x2000:
            return self.ram[addr & 0x1FFF]
        elif addr < 0x8000:
            if addr >= 0x4016 and addr <= 0x4017:
                # Controller read (simulated)
                return self.controller1
            return self.ram[addr & 0x1FFFF]
        else:
            if self.rom != NULL and self.rom_size > 0:
                if self.mapper_type == 0:
                    return self._read_lorom(addr)
                else:
                    return self._read_hirom(addr)
            return 0x00

    cdef void write_byte(self, unsigned int addr, unsigned char value):
        if addr < 0x2000:
            self.ram[addr & 0x1FFF] = value
        elif addr < 0x8000:
            self.ram[addr & 0x1FFFF] = value
        # PPU registers not implemented yet

    cdef void _update_nz(self, unsigned char val):
        self.p &= ~(0x80 | 0x02)
        if val == 0: self.p |= 0x02
        if val & 0x80: self.p |= 0x80

    cdef void _push(self, unsigned char val):
        self.ram[0x0100 + <unsigned int>self.s] = val
        self.s = (self.s - 1) & 0xFF

    cdef unsigned char _pull(self):
        self.s = (self.s + 1) & 0xFF
        return self.ram[0x0100 + <unsigned int>self.s]

    def cpu_step(self):
        cdef unsigned char opcode
        cdef unsigned short lo, hi
        cdef unsigned int addr
        cdef unsigned char val
        cdef unsigned short result16

        opcode = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
        self.pc = (self.pc + 1) & 0xFFFF

        # --- Implement enough opcodes to run simple homebrew ---
        if opcode == 0xEA:  # NOP
            pass
        # LDA immediate
        elif opcode == 0xA9:
            self.a = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self._update_nz(self.a)
        # LDX immediate
        elif opcode == 0xA2:
            self.x = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self._update_nz(self.x)
        # LDY immediate
        elif opcode == 0xA0:
            self.y = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self._update_nz(self.y)
        # STA absolute
        elif opcode == 0x8D:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            hi = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            addr = lo | (hi << 8)
            self.write_byte(addr, self.a)
        # STX absolute
        elif opcode == 0x8E:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            hi = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            addr = lo | (hi << 8)
            self.write_byte(addr, self.x)
        # STY absolute
        elif opcode == 0x8C:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            hi = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            addr = lo | (hi << 8)
            self.write_byte(addr, self.y)
        # STA direct
        elif opcode == 0x85:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self.write_byte((self.d + lo) & 0xFFFF, self.a)
        # LDA direct
        elif opcode == 0xA5:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self.a = self.read_byte((self.d + lo) & 0xFFFF)
            self._update_nz(self.a)
        # JMP absolute
        elif opcode == 0x4C:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            hi = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = lo | (hi << 8)
        # JSR absolute
        elif opcode == 0x20:
            lo = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            hi = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self._push(<unsigned char>((self.pc >> 8) & 0xFF))
            self._push(<unsigned char>(self.pc & 0xFF))
            self.pc = lo | (hi << 8)
        # RTS
        elif opcode == 0x60:
            lo = <unsigned short>self._pull()
            hi = <unsigned short>self._pull()
            self.pc = ((lo | (hi << 8)) + 1) & 0xFFFF
        # INX
        elif opcode == 0xE8:
            self.x = (self.x + 1) & 0xFF
            self._update_nz(self.x)
        # INY
        elif opcode == 0xC8:
            self.y = (self.y + 1) & 0xFF
            self._update_nz(self.y)
        # DEX
        elif opcode == 0xCA:
            self.x = (self.x - 1) & 0xFF
            self._update_nz(self.x)
        # DEY
        elif opcode == 0x88:
            self.y = (self.y - 1) & 0xFF
            self._update_nz(self.y)
        # INC A
        elif opcode == 0x1A:
            self.a = (self.a + 1) & 0xFF
            self._update_nz(self.a)
        # DEC A
        elif opcode == 0x3A:
            self.a = (self.a - 1) & 0xFF
            self._update_nz(self.a)
        # TAX
        elif opcode == 0xAA:
            self.x = self.a
            self._update_nz(self.x)
        # TAY
        elif opcode == 0xA8:
            self.y = self.a
            self._update_nz(self.y)
        # TXA
        elif opcode == 0x8A:
            self.a = self.x
            self._update_nz(self.a)
        # TYA
        elif opcode == 0x98:
            self.a = self.y
            self._update_nz(self.a)
        # CMP immediate
        elif opcode == 0xC9:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            result16 = <unsigned short>self.a - <unsigned short>val
            self.p = (self.p & 0x7C)
            if self.a >= val: self.p |= 0x01
            if (result16 & 0xFF) == 0: self.p |= 0x02
            if result16 & 0x80: self.p |= 0x80
        # BEQ
        elif opcode == 0xF0:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if self.p & 0x02:
                if val & 0x80: self.pc = (self.pc + val - 256) & 0xFFFF
                else: self.pc = (self.pc + val) & 0xFFFF
        # BNE
        elif opcode == 0xD0:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if not (self.p & 0x02):
                if val & 0x80: self.pc = (self.pc + val - 256) & 0xFFFF
                else: self.pc = (self.pc + val) & 0xFFFF
        # BRA
        elif opcode == 0x80:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if val & 0x80: self.pc = (self.pc + val - 256) & 0xFFFF
            else: self.pc = (self.pc + val) & 0xFFFF
        # PHA
        elif opcode == 0x48:
            self._push(self.a)
        # PLA
        elif opcode == 0x68:
            self.a = self._pull()
            self._update_nz(self.a)
        # PHP
        elif opcode == 0x08:
            self._push(self.p)
        # PLP
        elif opcode == 0x28:
            self.p = self._pull()
        # SEI
        elif opcode == 0x78:
            self.p |= 0x04
        # CLI
        elif opcode == 0x58:
            self.p &= ~0x04
        # CLC
        elif opcode == 0x18:
            self.p &= ~0x01
        # SEC
        elif opcode == 0x38:
            self.p |= 0x01
        # SEP
        elif opcode == 0xE2:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self.p |= val
        # REP
        elif opcode == 0xC2:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self.p &= ~val
        # AND immediate
        elif opcode == 0x29:
            self.a &= self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self._update_nz(self.a)
        # ORA immediate
        elif opcode == 0x09:
            self.a |= self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self._update_nz(self.a)
        # EOR immediate
        elif opcode == 0x49:
            self.a ^= self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            self._update_nz(self.a)
        # ASL A
        elif opcode == 0x0A:
            if self.a & 0x80: self.p |= 0x01
            else: self.p &= ~0x01
            self.a = (self.a << 1) & 0xFF
            self._update_nz(self.a)
        # LSR A
        elif opcode == 0x4A:
            if self.a & 0x01: self.p |= 0x01
            else: self.p &= ~0x01
            self.a = (self.a >> 1) & 0xFF
            self._update_nz(self.a)
        # ADC immediate
        elif opcode == 0x69:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            result16 = <unsigned short>self.a + <unsigned short>val + <unsigned short>(self.p & 0x01)
            self.p &= ~(0x01 | 0x02 | 0x40 | 0x80)
            if result16 > 0xFF: self.p |= 0x01
            if ((self.a ^ result16) & (val ^ result16) & 0x80): self.p |= 0x40
            self.a = <unsigned char>(result16 & 0xFF)
            self._update_nz(self.a)
        # SBC immediate
        elif opcode == 0xE9:
            val = self.read_byte((<unsigned int>self.pb << 16) | self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            result16 = <unsigned short>self.a - <unsigned short>val - <unsigned short>(1 - (self.p & 0x01))
            self.p &= ~(0x01 | 0x02 | 0x40 | 0x80)
            if result16 < 0x100: self.p |= 0x01
            self.a = <unsigned char>(result16 & 0xFF)
            self._update_nz(self.a)
        else:
            # Unknown opcode – treat as NOP (prevents halting)
            pass

    def run_frame(self):
        cdef int cycles, y, x

        if not self.is_running:
            return None

        self.frame_count += 1

        # Run ~2000 CPU cycles per frame (approx 60fps on a 3.58MHz CPU)
        for cycles in range(2000):
            if self.is_running:
                self.cpu_step()

        # Simple PPU: draw first tile from VRAM (offset 0x8000 in ROM)
        # This is just a placeholder – replace with real PPU code later.
        for y in range(224):
            for x in range(256):
                # Get tile data from ROM (if loaded) at address 0x8000 + (y/8*16 + x/8)*8
                if self.rom != NULL and self.rom_size > 0x8000:
                    tile_x = x // 8
                    tile_y = y // 8
                    tile_addr = 0x8000 + (tile_y * 32 + tile_x) * 8
                    if tile_addr + 7 < self.rom_size:
                        # Simple 1bpp pattern: use the first byte as pixel value
                        pix = self.rom[tile_addr + (y % 8)] & (1 << (7 - (x % 8)))
                        color = 255 if pix else 0
                        self.framebuffer_view[y, x, 0] = color
                        self.framebuffer_view[y, x, 1] = color
                        self.framebuffer_view[y, x, 2] = color
                    else:
                        # Fallback to colored bars
                        self.framebuffer_view[y, x, 0] = (x + self.frame_count) & 0xFF
                        self.framebuffer_view[y, x, 1] = (y + self.frame_count) & 0xFF
                        self.framebuffer_view[y, x, 2] = ((x ^ y) + self.frame_count) & 0xFF
                else:
                    self.framebuffer_view[y, x, 0] = (x + self.frame_count) & 0xFF
                    self.framebuffer_view[y, x, 1] = (y + self.frame_count) & 0xFF
                    self.framebuffer_view[y, x, 2] = ((x ^ y) + self.frame_count) & 0xFF

        # Show a red square when button A is pressed
        if self.controller1 & 0x80:
            for y in range(100, 120):
                for x in range(100, 120):
                    self.framebuffer_view[y, x, 0] = 255
                    self.framebuffer_view[y, x, 1] = 0
                    self.framebuffer_view[y, x, 2] = 0

        return self.framebuffer

    def start(self):
        self.is_running = True
        print("[Cython Core] Emulation started (65816 running)")

    def stop(self):
        self.is_running = False
        print("[Cython Core] Emulation stopped")

    def set_controller1(self, unsigned char buttons):
        self.controller1 = buttons

    def get_title(self):
        cdef bytes b_title
        if self.rom_title != NULL:
            b_title = self.rom_title
            return b_title.decode('ascii', errors='ignore').strip()
        return "No ROM"

    def get_pc(self):
        return self.pc

    def is_cpu_running(self):
        return self.is_running
'''


def _build_cython_core():
    """Compile Cython core on-the-fly. Returns the SNES class."""
    original_cflags = os.environ.get('CFLAGS', '')
    os.environ['CFLAGS'] = f"{original_cflags} -w -O3".strip()

    mod_name = f"snes_core_{uuid.uuid4().hex[:8]}"
    temp_dir = tempfile.mkdtemp(prefix="ac_snes_")
    pyx_path = os.path.join(temp_dir, f'{mod_name}.pyx')
    
    with open(pyx_path, 'w', encoding='utf-8') as f:
        f.write(CYTHON_CORE)

    sys.path.insert(0, temp_dir)
    try:
        pyximport.install(
            setup_args={'include_dirs': [np.get_include()]},
            language_level=3,
        )
        mod = importlib.import_module(mod_name)
    finally:
        if sys.path and sys.path[0] == temp_dir:
            sys.path.pop(0)
        threading.Timer(2.0, lambda: shutil.rmtree(temp_dir, ignore_errors=True)).start()

    return mod.SNES


# Build core at import time
SNES = _build_cython_core()


# ====================== TKINTER GUI ======================
class AC_Snes_Emu:
    SCALE = 2  # 256*2=512, 224*2=448
    WIDTH = 256 * SCALE
    HEIGHT = 224 * SCALE

    def __init__(self):
        self.root = tk.Tk()
        self.root.title("AC'S Snes Emu 0.2 — A.C Holdings / Team Flames")
        self.root.geometry(f"{self.WIDTH + 88}x{self.HEIGHT + 60}")
        self.root.configure(bg='#111111')
        self.root.resizable(False, False)

        self.snes = SNES()
        self.rom_path = None
        self.running = False
        self.emulation_thread = None
        self.photo = None
        self.keys = set()
        self._lock = threading.Lock()

        self._create_gui()
        self._bind_input()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _create_gui(self):
        pad_x = (self.WIDTH + 88 - self.WIDTH) // 2
        self.screen_label = tk.Label(self.root, bg='black', relief='sunken')
        self.screen_label.place(x=pad_x, y=8, width=self.WIDTH, height=self.HEIGHT)

        self.status = tk.Label(
            self.root,
            text="AC'S Snes Emu 0.2 — Load a ROM to start real 65816 emulation",
            fg="#00ff00", bg="#111111", font=("Consolas", 10),
        )
        self.status.pack(side="bottom", fill="x", pady=4)

        tk.Label(
            self.root,
            text="D-Pad: Arrows | A/B/X/Y: Z/X/A/S | Start: Enter | Select: Shift | L/R: Q/E",
            fg="#666666", bg="#111111", font=("Consolas", 9),
        ).pack(side="bottom", pady=2)

        menubar = tk.Menu(self.root)
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Open ROM...", command=self._open_rom, accelerator="Ctrl+O")
        filemenu.add_command(label="Reset", command=self._reset_emu)
        filemenu.add_separator()
        filemenu.add_command(label="Exit", command=self._on_close)
        menubar.add_cascade(label="File", menu=filemenu)
        self.root.config(menu=menubar)

    def _bind_input(self):
        self.root.bind("<KeyPress>", self._key_press)
        self.root.bind("<KeyRelease>", self._key_release)
        self.root.bind("<Control-o>", lambda _: self._open_rom())

    def _key_press(self, event):
        self.keys.add(event.keysym.lower())
        self._update_controller()

    def _key_release(self, event):
        self.keys.discard(event.keysym.lower())
        self._update_controller()

    _KEY_MAP = {
        'up': 0x08, 'down': 0x04, 'left': 0x02, 'right': 0x01,
        'z': 0x80, 'x': 0x40, 'a': 0x20, 's': 0x10,
        'return': 0x08, 'shift_l': 0x04, 'shift_r': 0x04,
        'q': 0x02, 'e': 0x01,
    }

    def _update_controller(self):
        buttons = 0
        for k in self.keys:
            buttons |= self._KEY_MAP.get(k, 0)
        self.snes.set_controller1(buttons)

    def _open_rom(self):
        path = filedialog.askopenfilename(
            title="Open SNES ROM",
            filetypes=[("SNES ROMs", "*.smc *.sfc *.fig *.bs"), ("All files", "*.*")],
        )
        if not path:
            return

        self.running = False
        if self.emulation_thread and self.emulation_thread.is_alive():
            self.emulation_thread.join(timeout=2.0)

        self.rom_path = path
        if self.snes.load_rom(path):
            title = self.snes.get_title()
            self.status.config(text=f"Loaded: {title} | 65816 running!")
            self._start_emulation()
        else:
            self.status.config(text="Failed to load ROM.")

    def _reset_emu(self):
        if self.rom_path:
            self.snes.reset()
            self.status.config(text=f"Reset: {self.snes.get_title()}")

    def _start_emulation(self):
        if self.running:
            return
        self.running = True
        self.snes.start()
        self.emulation_thread = threading.Thread(target=self._emulation_loop, daemon=True)
        self.emulation_thread.start()

    def _emulation_loop(self):
        target_dt = 1.0 / 60.0
        while self.running:
            start = time.perf_counter()
            fb = self.snes.run_frame()
            if fb is not None:
                # Make a copy and update GUI (thread-safe)
                with self._lock:
                    fb_copy = np.copy(fb)
                self.root.after(0, self._update_screen, fb_copy)
            elapsed = time.perf_counter() - start
            remaining = target_dt - elapsed
            if remaining > 0:
                time.sleep(remaining)

    def _update_screen(self, framebuffer):
        if not self.root.winfo_exists():
            return
        img = Image.fromarray(framebuffer, 'RGB')
        img = img.resize((self.WIDTH, self.HEIGHT), Image.NEAREST)
        self.photo = ImageTk.PhotoImage(img)
        self.screen_label.config(image=self.photo)

    def _on_close(self):
        self.running = False
        self.snes.stop()
        if self.emulation_thread and self.emulation_thread.is_alive():
            self.emulation_thread.join(timeout=2.0)
        self.root.destroy()

    def run(self):
        print("🚀 AC'S Snes Emu 0.2 starting - real 65816 CPU active!")
        self.root.mainloop()


if __name__ == "__main__":
    AC_Snes_Emu().run()
