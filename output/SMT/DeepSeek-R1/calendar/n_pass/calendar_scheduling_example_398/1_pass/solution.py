from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 30
    
    # Total available time window: 9:00 (0 min) to 17:00 (480 min)
    s.add(start >= 0)
    s.add(start <= 480 - duration)  # Meeting must end by 17:00 (480 min)
    
    # Blocked intervals for each participant (in minutes from 9:00)
    # Doris: [0, 120], [270, 300], [420, 450]
    doris_intervals = [(0, 120), (270, 300), (420, 450)]
    
    # Theresa: [60, 180]
    theresa_intervals = [(60, 180)]
    
    # Christian: no meetings
    christian_intervals = []
    
    # Terry: [30, 60), [150, 180), [210, 240), [270, 300), [330, 360), [390, 480)
    terry_intervals = [(30, 60), (150, 180), (210, 240), (270, 300), (330, 360), (390, 480)]
    
    # Carolyn: [0, 90), [120, 150), [180, 240), [270, 330), [360, 480)
    carolyn_intervals = [(0, 90), (120, 150), (180, 240), (270, 330), (360, 480)]
    
    # Kyle: [0, 30), [150, 180), [210, 240), [330, 480)
    kyle_intervals = [(0, 30), (150, 180), (210, 240), (330, 480)]
    
    # Combine all participants' intervals
    all_intervals = {
        'Doris': doris_intervals,
        'Theresa': theresa_intervals,
        'Christian': christian_intervals,
        'Terry': terry_intervals,
        'Carolyn': carolyn_intervals,
        'Kyle': kyle_intervals
    }
    
    # For each participant and each of their intervals, add constraints
    for participant, intervals in all_intervals.items():
        for interval in intervals:
            a, b = interval
            # The meeting must not overlap with [a, b]: either meeting ends before a or starts after b
            s.add(Or(start + duration <= a, start >= b))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Convert start_min back to time string
        hours = 9 + start_min // 60
        minutes = start_min % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        hours_end = 9 + end_min // 60
        minutes_end = end_min % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()