from z3 import *

def main():
    s = Solver()
    duration = 30
    total_time = 480  # 9:00-17:00 in minutes
    start = Int('start')
    
    # Constraint: start time within [0, 450] and multiple of 30 minutes
    s.add(start >= 0, start <= total_time - duration)
    s.add(start % 30 == 0)
    
    # Convert busy times to minutes (relative to 9:00)
    jack_busy = [(0, 30), (300, 330)]
    madison_busy = [(30, 90), (240, 300), (360, 390), (450, 480)]
    rachel_busy = [(30, 90), (120, 150), (180, 270), (330, 390), (420, 480)]
    douglas_busy = [(0, 150), (180, 450)]
    ryan_busy = [(0, 30), (240, 300), (330, 480)]
    
    # Combine all constraints
    all_busy = jack_busy + madison_busy + rachel_busy + douglas_busy + ryan_busy
    
    for (b_start, b_end) in all_busy:
        # Meeting must not overlap: either before or after busy interval
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