from z3 import Solver, Int, Or

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    meeting_duration = 60  # in minutes
    # Represent time as minutes since midnight.
    # 9:00 = 540 and 17:00 = 1020, so start must be between 540 and 1020 - duration.
    s = Int('s')
    
    solver = Solver()
    # Domain constraints: meeting must start no earlier than 9:00 and finish by 17:00.
    solver.add(s >= 540, s + meeting_duration <= 1020)
    
    # Busy intervals for each participant (times are in minutes since midnight)
    # Julie's busy times: 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 16:00-17:00
    julie_busy = [(540, 570), (660, 690), (720, 750), (810, 840), (960, 1020)]
    # Sean's busy times: 9:00-9:30, 13:00-13:30, 15:00-15:30, 16:00-16:30
    sean_busy = [(540, 570), (780, 810), (900, 930), (960, 990)]
    # Lori's busy times: 10:00-10:30, 11:00-13:00, 15:30-17:00
    lori_busy = [(600, 630), (660, 780), (930, 1020)]
    
    # For the meeting to not conflict with a busy interval [a, b],
    # it must finish before a or start after the busy period ends.
    def no_conflict(s, a, b):
        return Or(s + meeting_duration <= a, s >= b)
    
    # Add constraints for all busy intervals from every participant.
    for (a, b) in (julie_busy + sean_busy + lori_busy):
        solver.add(no_conflict(s, a, b))
    
    if solver.check() == 'sat':
        model = solver.model()
        start_time = model[s].as_long()
        end_time = start_time + meeting_duration
        
        # Format times as HH:MM (24-hour clock)
        formatted_start = minutes_to_time(start_time)
        formatted_end   = minutes_to_time(end_time)
        
        # Print the solution, following the required format.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time:", formatted_start)
        print("End Time:", formatted_end)
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()