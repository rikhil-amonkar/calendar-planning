from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize Z3 optimizer (instead of Solver)
    opt = Optimize()

    # Define travel times (in minutes)
    travel_times = {
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'The Castro'): 22,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'The Castro'): 7,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Mission District'): 7,
    }

    # Define friend availability
    james_available_start = datetime.datetime.strptime("12:45", "%H:%M")
    james_available_end = datetime.datetime.strptime("14:00", "%H:%M")
    robert_available_start = datetime.datetime.strptime("12:45", "%H:%M")
    robert_available_end = datetime.datetime.strptime("15:15", "%H:%M")

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        time = datetime.datetime.strptime(time_str, "%H:%M")
        return (time.hour - 9) * 60 + time.minute

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    meet_james_start = Int('meet_james_start')
    meet_james_end = Int('meet_james_end')
    meet_robert_start = Int('meet_robert_start')
    meet_robert_end = Int('meet_robert_end')

    # Constraints for James
    opt.add(meet_james_start >= time_to_minutes("12:45"))
    opt.add(meet_james_end <= time_to_minutes("14:00"))
    opt.add(meet_james_end - meet_james_start >= 75)  # At least 75 minutes

    # Constraints for Robert
    opt.add(meet_robert_start >= time_to_minutes("12:45"))
    opt.add(meet_robert_end <= time_to_minutes("15:15"))
    opt.add(meet_robert_end - meet_robert_start >= 30)  # At least 30 minutes

    # Define variables for locations before and after meetings
    # 0: North Beach, 1: Mission District, 2: The Castro
    before_james = Int('before_james')  # Location before meeting James
    after_james = Int('after_james')    # Location after meeting James
    before_robert = Int('before_robert') # Location before meeting Robert
    after_robert = Int('after_robert')   # Location after meeting Robert

    # Initial location is North Beach (0)
    opt.add(before_james == 0)

    # James is at Mission District (1), Robert is at The Castro (2)
    opt.add(after_james == 1)  # Meeting James at Mission District
    opt.add(after_robert == 2) # Meeting Robert at The Castro

    # Travel constraints
    # Time to reach James must account for travel
    opt.add(meet_james_start >= travel_times[('North Beach', 'Mission District')])

    # Time to reach Robert must account for travel from James or elsewhere
    # We'll add both possibilities and let the solver choose

    # Option 1: Meet James first, then Robert
    option1 = And(
        before_robert == 1,  # After meeting James, we're at Mission District
        meet_robert_start >= meet_james_end + travel_times[('Mission District', 'The Castro')]
    )

    # Option 2: Meet Robert first, then James
    option2 = And(
        before_james == 2,  # After meeting Robert, we're at The Castro
        meet_james_start >= meet_robert_end + travel_times[('The Castro', 'Mission District')],
        meet_robert_start >= travel_times[('North Beach', 'The Castro')]
    )

    opt.add(Or(option1, option2))

    # Ensure no overlapping meetings
    opt.add(Or(
        meet_james_end <= meet_robert_start,
        meet_robert_end <= meet_james_start
    ))

    # Maximize total meeting time
    total_meeting_time = (meet_james_end - meet_james_start) + (meet_robert_end - meet_robert_start)
    opt.maximize(total_meeting_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        james_start = m.eval(meet_james_start).as_long()
        james_end = m.eval(meet_james_end).as_long()
        robert_start = m.eval(meet_robert_start).as_long()
        robert_end = m.eval(meet_robert_end).as_long()

        # Determine the order of meetings
        if james_end <= robert_start:
            itinerary = [
                {"action": "meet", "person": "James", "start_time": minutes_to_time(james_start), "end_time": minutes_to_time(james_end)},
                {"action": "meet", "person": "Robert", "start_time": minutes_to_time(robert_start), "end_time": minutes_to_time(robert_end)}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Robert", "start_time": minutes_to_time(robert_start), "end_time": minutes_to_time(robert_end)},
                {"action": "meet", "person": "James", "start_time": minutes_to_time(james_start), "end_time": minutes_to_time(james_end)}
            ]

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve and print the solution
solution = solve_scheduling_problem()
print(solution)