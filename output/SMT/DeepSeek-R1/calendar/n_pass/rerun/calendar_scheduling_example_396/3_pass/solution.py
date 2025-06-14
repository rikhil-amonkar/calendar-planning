from z3 import *

def main():
    s = Solver()
    duration = 30
    total_time = 480  # 9:00-17:00 in minutes
    start = Int('start')
    
    # Start time must be between 0 and 450 (inclusive) and multiple of 30 minutes
    s.add(start >= 0, start <= total_time - duration)
    s.add(start % 30 == 0)
    
    # Convert busy times to minutes (relative to 9:00) with 1-minute buffers
    jack_busy = [(0, 31), (299, 331)]        # 9:00-9:30 and 14:00-14:30 with buffers
    madison_busy = [(29, 91), (239, 301), (359, 391), (449, 480)]  # Buffered intervals
    rachel_busy = [(29, 91), (119, 151), (179, 271), (329, 391), (419, 480)]
    douglas_busy = [(0, 151), (179, 451)]    # Buffered 9:00-11:30 and 12:00-16:30
    ryan_busy = [(0, 31), (239, 301), (329, 480)]
    
    # Combine all constraints
    all_busy = jack_busy + madison_busy + rachel_busy + douglas_busy + ryan_busy
    
    for (b_start, b_end) in all_busy:
        # Meeting must not overlap with buffered busy intervals
        s.add(Or(start + duration <= b_start, start >= b_end))
    
    if s.check() == sat:
        m = s.model()
        start_min = m.eval(start).as_long()
        h = 9 + start_min // 60
        m_min = start_min % 60
        end_min = start_min + duration
        h_end = 9 + end_min // 60
        m_end = end_min % 60
        print(f"Meeting can be scheduled from {h:02d}:{m_min:02d} to {h_end:02d}:{m_end:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()