from z3 import *

def schedule_meetings(num_people, num_meetings, meeting_durations, working_hours, fixed_times, required_meetings, min_duration):
    s = Solver()
    
    # Create time variables for each meeting and person
    t = {}
    for i in range(num_meetings):
        for j in range(num_people):
            t[(i, j)] = Real(f't_{i}_{j}')
    
    # Create variables for meetings (whether meeting i happens for person j)
    meet = {}
    for i in range(num_meetings):
        for j in range(num_people):
            meet[(i, j)] = Bool(f'meet_{i}_{j}')
    
    # Create variables for meeting days (which day meeting i occurs)
    day_of_meeting = [Int(f'day_{i}') for i in range(num_meetings)]
    
    # Constraints for each meeting
    for i in range(num_meetings):
        min_dur = meeting_durations[i]
        
        # Ensure meeting day is valid for all participants
        for j in range(num_people):
            num_days_j = len(working_hours[j])
            s.add(day_of_meeting[i] >= 0, day_of_meeting[i] < num_days_j)
            
        # Constraints for each person for meeting i
        for j in range(num_people):
            fidx = (i, j)
            if fidx in fixed_times:
                start_win, end_win = fixed_times[fidx]
                # If meeting happens, it must be within fixed time window
                s.add(If(meet[fidx], 
                         And(t[fidx] >= start_win, t[fidx] + min_dur <= end_win), 
                         True))
            else:
                # Build time window based on working hours for the meeting day
                num_days_j = len(working_hours[j])
                # Start with day 0
                cond_start = working_hours[j][0][0]
                cond_end = working_hours[j][0][1]
                # Chain If-expressions for subsequent days
                for d in range(1, num_days_j):
                    cond_start = If(day_of_meeting[i] == d, working_hours[j][d][0], cond_start)
                    cond_end = If(day_of_meeting[i] == d, working_hours[j][d][1], cond_end)
                # If meeting happens, it must be within working hours
                s.add(If(meet[fidx], 
                         And(t[fidx] >= cond_start, t[fidx] + min_dur <= cond_end), 
                         True))
        
        # Required meetings must have all participants
        if required_meetings[i]:
            for j in range(num_people):
                s.add(meet[(i, j)])
        else:
            # Optional meetings need at least one participant
            s.add(Or([meet[(i, j)] for j in range(num_people)]))
    
    # Prevent overlapping meetings for each person
    for j in range(num_people):
        for i1 in range(num_meetings):
            for i2 in range(i1 + 1, num_meetings):
                # Only check if both meetings are attended
                both_attended = And(meet[(i1, j)], meet[(i2, j)])
                # Only check overlaps if on same day
                same_day = (day_of_meeting[i1] == day_of_meeting[i2])
                # Ensure time doesn't overlap if same day
                no_overlap = Or(
                    t[(i1, j)] + meeting_durations[i1] <= t[(i2, j)],
                    t[(i2, j)] + meeting_durations[i2] <= t[(i1, j)]
                )
                # Add conditional constraint
                s.add(If(both_attended, 
                         If(same_day, no_overlap, True), 
                         True))
    
    # Solve and return schedule if possible
    if s.check() == sat:
        model = s.model()
        schedule = {}
        for i in range(num_meetings):
            for j in range(num_people):
                if model.evaluate(meet[(i, j)]):
                    time_val = model.evaluate(t[(i, j)])
                    # Extract numerical value if possible
                    if is_algebraic_value(time_val):
                        schedule[(i, j)] = time_val.approx(7).as_decimal(3)
                    else:
                        schedule[(i, j)] = str(time_val)
        return schedule
    else:
        return None

# Example usage with 9 people
if __name__ == "__main__":
    num_people = 9
    num_meetings = 2
    meeting_durations = [1, 2]
    # Working hours: 5 days (0 to 4) for each person, 9am-5pm
    working_hours = [
        [(9, 17), (9, 17), (9, 17), (9, 17), (9, 17)] 
        for _ in range(9)
    ]
    fixed_times = {
        (0, 0): (9, 10),  # Meeting 0, Person 0 must have fixed time 9-10
        (0, 1): (10, 12)   # Meeting 0, Person 1 must have fixed time 10-12
    }
    required_meetings = [True, False]  # Meeting 0 is required for all, meeting 1 is optional
    
    min_duration = 1
    
    schedule = schedule_meetings(num_people, num_meetings, meeting_durations, working_hours, fixed_times, required_meetings, min_duration)
    if schedule:
        print("Meeting schedule:")
        for (i, j), time in schedule.items():
            print(f"Meeting {i} with person {j} at time {time}")
    else:
        print("No schedule found.")