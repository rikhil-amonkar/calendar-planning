from z3 import *

def main():
    # Initialize solver with optimization capabilities
    s = Optimize()

    # Define variables for meeting times (start and end for each day)
    meeting_start_mon, meeting_end_mon = Int('meeting_start_mon'), Int('meeting_end_mon')
    meeting_start_tue, meeting_end_tue = Int('meeting_start_tue'), Int('meeting_end_tue')
    meeting_start_wed, meeting_end_wed = Int('meeting_start_wed'), Int('meeting_end_wed')
    meeting_start_thu, meeting_end_thu = Int('meeting_start_thu'), Int('meeting_end_thu')
    meeting_start_fri, meeting_end_fri = Int('meeting_start_fri'), Int('meeting_end_fri')

    # Define domain constraints (each meeting must be within working hours: 8:00 to 17:00)
    time_min = 8 * 60  # 8:00 AM in minutes
    time_max = 17 * 60 # 5:00 PM in minutes

    days = [
        (meeting_start_mon, meeting_end_mon),
        (meeting_start_tue, meeting_end_tue),
        (meeting_start_wed, meeting_end_wed),
        (meeting_start_thu, meeting_end_thu),
        (meeting_start_fri, meeting_end_fri)
    ]

    for start, end in days:
        s.add(start >= time_min, end <= time_max, end - start >= 60)  # Meetings must be at least 1 hour

    # Define specific constraints for each person's availability
    # Person A: Monday (8:00-12:00), Wednesday (10:00-15:00)
    s.add(Or(
        And(meeting_start_mon >= 8*60, meeting_end_mon <= 12*60),
        And(meeting_start_wed >= 10*60, meeting_end_wed <= 15*60)
    ))

    # Person B: Tuesday (9:00-11:00), Thursday (14:00-16:00)
    s.add(Or(
        And(meeting_start_tue >= 9*60, meeting_end_tue <= 11*60),
        And(meeting_start_thu >= 14*60, meeting_end_thu <= 16*60)
    ))

    # Person C: Monday (13:00-17:00), Friday (8:00-10:00)
    s.add(Or(
        And(meeting_start_mon >= 13*60, meeting_end_mon <= 17*60),
        And(meeting_start_fri >= 8*60, meeting_end_fri <= 10*60)
    ))

    # Person D: Tuesday (13:00-15:00), Wednesday (8:00-12:00)
    s.add(Or(
        And(meeting_start_tue >= 13*60, meeting_end_tue <= 15*60),
        And(meeting_start_wed >= 8*60, meeting_end_wed <= 12*60)
    ))

    # Person E: Wednesday (14:00-17:00), Friday (13:00-17:00)
    s.add(Or(
        And(meeting_start_wed >= 14*60, meeting_end_wed <= 17*60),
        And(meeting_start_fri >= 13*60, meeting_end_fri <= 17*60)
    ))

    # Objective: Maximize the total meeting time across all days
    total_meeting_time = Sum([end - start for start, end in days])
    s.maximize(total_meeting_time)

    # Check satisfiability and print the solution
    if s.check() == sat:
        m = s.model()
        days_str = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
        for i, day in enumerate(days_str):
            start_val = m.evaluate(days[i][0]).as_long()
            end_val = m.evaluate(days[i][1]).as_long()
            start_hr = start_val // 60
            start_min = start_val % 60
            end_hr = end_val // 60
            end_min = end_val % 60
            print(f"{day}: {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()