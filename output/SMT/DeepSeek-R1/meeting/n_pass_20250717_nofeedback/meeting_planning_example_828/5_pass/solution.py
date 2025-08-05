from z3 import *

def main():
    # Initialize variables for start times (in minutes from 9:00)
    start_A, start_B, start_C, start_D, start_E = Ints('start_A start_B start_C start_D start_E')
    
    # Durations in minutes
    dur_A = 180  # 3 hours
    dur_B = 120  # 2 hours
    dur_C = 120  # 2 hours
    dur_D = 60   # 1 hour
    dur_E = 60   # 1 hour
    
    s = Solver()
    
    # Time window constraints (9:00 to 17:00, which is 480 minutes)
    s.add(start_A >= 0, start_A + dur_A <= 480)
    s.add(start_B >= 0, start_B + dur_B <= 480)
    s.add(start_C >= 0, start_C + dur_C <= 480)
    s.add(start_D >= 0, start_D + dur_D <= 480)
    s.add(start_E >= 0, start_E + dur_E <= 480)
    
    # Constraints for A, B, C: must finish by 12:00 (180 minutes) OR start at or after 13:00 (240 minutes? But note: 13:00 is 240 minutes from 9:00? Actually 13:00 is 4 hours after 9:00 -> 4*60=240 minutes? But 12:00 is 3 hours -> 180 minutes.
    # Correction: 13:00 is 4 hours from 9:00? Actually: 9:00 to 13:00 is 4 hours -> 240 minutes. However, the constraint says "starts no earlier than 13:00", which is 240 minutes.
    # But note: 12:00 is 180 minutes from 9:00. So:
    s.add(Or(start_A + dur_A <= 180, start_A >= 240))  # 13:00 is 240 minutes from 9:00
    s.add(Or(start_B + dur_B <= 180, start_B >= 240))
    s.add(Or(start_C + dur_C <= 180, start_C >= 240))
    
    # Constraint for D: must start exactly at 12:00 (which is 180 minutes from 9:00)
    s.add(start_D == 180)
    
    # Constraint for E: must start at 10:00 (60), 12:00 (180), or 14:00 (240)
    s.add(Or(start_E == 60, start_E == 180, start_E == 240))
    
    # Non-overlapping constraints
    meetings = [
        (start_A, dur_A, 'A'),
        (start_B, dur_B, 'B'),
        (start_C, dur_C, 'C'),
        (start_D, dur_D, 'D'),
        (start_E, dur_E, 'E')
    ]
    
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            s1, d1, _ = meetings[i]
            s2, d2, _ = meetings[j]
            s.add(Or(s1 + d1 <= s2, s2 + d2 <= s1))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        # Function to convert minutes to time string
        def min_to_time(min_val):
            hours = 9 + min_val // 60
            minutes = min_val % 60
            return f"{hours:02d}:{minutes:02d}"
        
        # Collect the schedule
        schedule = []
        for var, dur, person in meetings:
            start_val = m[var].as_long()
            end_val = start_val + dur
            schedule.append({
                'action': 'meet',
                'person': f'Person {person}',
                'start_time': min_to_time(start_val),
                'end_time': min_to_time(end_val)
            })
        
        # Format the output
        plan = {'itinerary': schedule}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()