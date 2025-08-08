from z3 import *

def min_to_time(mins):
    total_minutes = 540 + mins  # 9:00 AM is 540 minutes from midnight
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Try order1: Richard then Charles
    R_start = Int('R_start')
    R_dur = Int('R_dur')
    C_start = Int('C_start')
    C_dur = Int('C_dur')
    
    s = Solver()
    # Fix R_start to 17 minutes (arrival at Union Square at 9:17 AM)
    s.add(R_start == 17)
    # Charles must start at or after 9:45 AM (45 minutes) and after traveling from Union Square
    s.add(C_start >= 45)
    s.add(C_start >= R_start + R_dur + 24)  # Travel time from Union Square to Presidio
    # Meeting durations must be at least 1 minute
    s.add(R_dur >= 1, C_dur >= 1)
    # Meetings must end by 1:00 PM (240 minutes)
    s.add(R_start + R_dur <= 240)
    s.add(C_start + C_dur <= 240)
    # At least one meeting must be 120 minutes or more
    s.add(Or(R_dur >= 120, C_dur >= 120))
    # Maximize Charles' meeting time by setting it to end at 1:00 PM
    s.add(C_dur == 240 - C_start)
    
    if s.check() == sat:
        m = s.model()
        R_start_val = m.eval(R_start).as_long()
        R_dur_val = m.eval(R_dur).as_long()
        C_start_val = m.eval(C_start).as_long()
        C_dur_val = m.eval(C_dur).as_long()
        
        itinerary = [
            {
                "action": "meet",
                "person": "Richard",
                "start_time": min_to_time(R_start_val),
                "end_time": min_to_time(R_start_val + R_dur_val)
            },
            {
                "action": "meet",
                "person": "Charles",
                "start_time": min_to_time(C_start_val),
                "end_time": min_to_time(C_start_val + C_dur_val)
            }
        ]
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        # Fallback to Option 2 if Option 1 is not feasible (though it should be)
        R_start = Int('R_start2')
        R_dur = Int('R_dur2')
        C_start = Int('C_start2')
        C_dur = Int('C_dur2')
        
        s2 = Solver()
        s2.add(C_start == 45)  # Charles starts at 9:45 AM
        s2.add(R_start == C_start + C_dur + 22)  # Travel time from Presidio to Union Square
        s2.add(R_dur == 173 - C_dur)  # Derived from total meeting time constraint
        s2.add(R_dur >= 1, C_dur >= 1)
        s2.add(Or(R_dur >= 120, C_dur >= 120))
        s2.add(R_start + R_dur <= 240)
        
        if s2.check() == sat:
            m = s2.model()
            R_start_val = m.eval(R_start).as_long()
            R_dur_val = m.eval(R_dur).as_long()
            C_start_val = m.eval(C_start).as_long()
            C_dur_val = m.eval(C_dur).as_long()
            
            itinerary = [
                {
                    "action": "meet",
                    "person": "Charles",
                    "start_time": min_to_time(C_start_val),
                    "end_time": min_to_time(C_start_val + C_dur_val)
                },
                {
                    "action": "meet",
                    "person": "Richard",
                    "start_time": min_to_time(R_start_val),
                    "end_time": min_to_time(R_start_val + R_dur_val)
                }
            ]
            print('SOLUTION:')
            print(f'{{"itinerary": {itinerary}}}')
        else:
            # If no solution is found, meet only one friend (not required per analysis)
            print("SOLUTION: {\"itinerary\": []}")

if __name__ == "__main__":
    main()