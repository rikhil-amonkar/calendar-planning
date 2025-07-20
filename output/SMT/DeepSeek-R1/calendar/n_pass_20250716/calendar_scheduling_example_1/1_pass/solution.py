from z3 import Solver, Int, Or, And, sat

def main():
    # Convert time to minutes from 9:00 (e.g., 9:30 -> 30 minutes)
    raymond_blocks = [(0, 30), (150, 180), (240, 270), (360, 390)]
    billy_blocks = [(60, 90), (180, 240), (450, 480)]
    donald_blocks = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]
    
    s = Solver()
    start = Int('start')
    duration = 30
    
    # Constraint: meeting must be within 9:00 to 17:00
    s.add(start >= 0)
    s.add(start <= 480 - duration)
    
    # Function to add no-overlap constraints for a participant's blocks
    def add_no_overlap_constraints(blocks):
        for b_start, b_end in blocks:
            s.add(Or(start + duration <= b_start, start >= b_end))
    
    add_no_overlap_constraints(raymond_blocks)
    add_no_overlap_constraints(billy_blocks)
    add_no_overlap_constraints(donald_blocks)
    
    # First, try to meet Billy's preference: end by 15:00 (360 minutes)
    s.push()
    s.add(start + duration <= 360)
    
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        s.pop()
    else:
        s.pop()
        # No solution before 15:00; try any time
        if s.check() == sat:
            m = s.model()
            start_val = m[start].as_long()
        else:
            # According to the problem, a solution exists
            raise Exception("No solution found, but one should exist")
    
    # Convert start_val to time string
    total_minutes = start_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours}:{minutes:02d}"
    
    end_val = start_val + duration
    total_minutes_end = end_val
    hours_end = 9 + total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_time = f"{hours_end}:{minutes_end:02d}"
    
    print(f"Monday, {start_time}, {end_time}")

if __name__ == "__main__":
    main()