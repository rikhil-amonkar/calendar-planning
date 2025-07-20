from z3 import *

def main():
    s = Solver()
    duration = 30
    total_time = 480  # 9:00 to 17:00 in minutes
    start = Int('start')
    
    # Start time must be a multiple of 30 between 0 and 450 inclusive
    s.add(start >= 0, start <= total_time - duration)
    s.add(start % 30 == 0)
    
    # Busy times in minutes (half-open intervals [start, end))
    jack_busy = [(0, 30), (300, 330)]
    madison_busy = [(30, 120), (240, 300), (360, 390), (450, 480)]
    rachel_busy = [(30, 120), (150, 210), (270, 360), (390, 480)]
    douglas_busy = [(0, 150), (180, 360)]
    ryan_busy = [(0, 30), (240, 300), (390, 480)]
    
    all_busy = jack_busy + madison_busy + rachel_busy + douglas_busy + ryan_busy
    
    # Ensure meeting [start, start+duration) does not overlap with any busy interval
    for (busy_start, busy_end) in all_busy:
        s.add(Or(start + duration <= busy_start, start >= busy_end))
    
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