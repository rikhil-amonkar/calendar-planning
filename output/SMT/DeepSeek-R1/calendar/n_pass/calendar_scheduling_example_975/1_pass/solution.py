from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return (hours - 9) * 60 + minutes

def main():
    # Preprocess Nicole's meetings
    nicole_meetings = {
        1: [("16:00", "16:30")],    # Tuesday
        2: [("15:00", "15:30")],    # Wednesday
        4: [("12:00", "12:30"), ("15:30", "16:00")]  # Friday
    }
    
    # Preprocess Daniel's meetings
    daniel_meetings = {
        0: [("9:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],  # Monday
        1: [("9:00", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],  # Tuesday
        2: [("9:00", "10:00"), ("11:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],  # Wednesday
        3: [("11:00", "12:00"), ("13:00", "14:00"), ("15:00", "15:30")],  # Thursday
        4: [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")]  # Friday
    }
    
    # Convert time strings to minutes for Nicole
    nicole_busy = {}
    for day, intervals in nicole_meetings.items():
        nicole_busy[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    
    # Convert time strings to minutes for Daniel
    daniel_busy = {}
    for day, intervals in daniel_meetings.items():
        daniel_busy[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    
    # Z3 variables
    day = Int('day')
    start = Int('start')
    
    s = Optimize()
    
    # Day must be between 0 (Monday) and 4 (Friday)
    s.add(day >= 0, day <= 4)
    # Start time must allow the meeting to end by 17:00 (480 minutes from 9:00)
    s.add(start >= 0, start <= 420)
    
    # Constraints per day
    constraints = []
    for d in range(5):
        # Nicole's busy intervals on day d
        nicole_conds = []
        if d in nicole_busy:
            for s_busy, e_busy in nicole_busy[d]:
                nicole_conds.append(Or(start >= e_busy, start + 60 <= s_busy))
        else:
            nicole_conds = [True]  # No meetings, so condition always true
        
        # Daniel's busy intervals on day d
        daniel_conds = []
        if d in daniel_busy:
            for s_busy, e_busy in daniel_busy[d]:
                daniel_conds.append(Or(start >= e_busy, start + 60 <= s_busy))
        else:
            daniel_conds = [True]  # No meetings, so condition always true
        
        # Combined conditions for day d
        day_constraint = And(And(nicole_conds), And(daniel_conds))
        constraints.append(If(day == d, day_constraint, True))
    
    s.add(And(constraints))
    
    # Minimize: earliest day and then earliest start time
    s.minimize(day * 480 + start)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_minutes = m[start].as_long()
        
        # Convert day index to name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[d_val]
        
        # Calculate start time in HH:MM
        total_minutes_start = start_minutes
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time in HH:MM
        end_minutes = start_minutes + 60
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the result
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found, but the problem states there is one.")

if __name__ == "__main__":
    main()