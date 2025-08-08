from z3 import *

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define variables for meeting start and end times
    # Meeting with Laura
    laura_start = Int('laura_start')  # in minutes
    laura_end = Int('laura_end')      # in minutes

    # Meeting with Anthony
    anthony_start = Int('anthony_start')  # in minutes
    anthony_end = Int('anthony_end')      # in minutes

    # Laura's availability: 12:15 to 19:45 (12:15PM to 7:45PM)
    laura_available_start = 12 * 60 + 15
    laura_available_end = 19 * 60 + 45

    # Anthony's availability: 12:30 to 14:45 (12:30PM to 2:45PM)
    anthony_available_start = 12 * 60 + 30
    anthony_available_end = 14 * 60 + 45

    # Minimum meeting durations
    laura_min_duration = 75
    anthony_min_duration = 30

    # Travel times in minutes
    castro_to_mission = 7
    castro_to_financial = 20
    mission_to_financial = 17
    financial_to_mission = 17

    # Constraints for Laura's meeting
    opt.add(laura_start >= laura_available_start)
    opt.add(laura_end <= laura_available_end)
    opt.add(laura_end - laura_start >= laura_min_duration)

    # Constraints for Anthony's meeting
    opt.add(anthony_start >= anthony_available_start)
    opt.add(anthony_end <= anthony_available_end)
    opt.add(anthony_end - anthony_start >= anthony_min_duration)

    # Initial location: The Castro at 9:00 AM (540 minutes)
    # We need to decide the order of meetings: Laura first or Anthony first

    # Option 1: Meet Laura first, then Anthony
    # Travel from Castro to Mission: 7 minutes
    # Then from Mission to Financial: 17 minutes
    option1_meet_laura_first = And(
        laura_start >= 540 + castro_to_mission,
        anthony_start >= laura_end + mission_to_financial
    )

    # Option 2: Meet Anthony first, then Laura
    # Travel from Castro to Financial: 20 minutes
    # Then from Financial to Mission: 17 minutes
    option2_meet_anthony_first = And(
        anthony_start >= 540 + castro_to_financial,
        laura_start >= anthony_end + financial_to_mission
    )

    # Choose one of the options
    opt.add(Or(option1_meet_laura_first, option2_meet_anthony_first))

    # Maximize the total meeting time
    total_time = (laura_end - laura_start) + (anthony_end - anthony_start)
    opt.maximize(total_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        # Extract meeting times
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        laura_start_time = minutes_to_time(m.evaluate(laura_start).as_long())
        laura_end_time = minutes_to_time(m.evaluate(laura_end).as_long())
        anthony_start_time = minutes_to_time(m.evaluate(anthony_start).as_long())
        anthony_end_time = minutes_to_time(m.evaluate(anthony_end).as_long())

        # Determine the order of meetings
        laura_start_min = m.evaluate(laura_start).as_long()
        anthony_start_min = m.evaluate(anthony_start).as_long()

        itinerary = []
        if laura_start_min < anthony_start_min:
            itinerary.append({
                "action": "meet",
                "person": "Laura",
                "start_time": laura_start_time,
                "end_time": laura_end_time
            })
            itinerary.append({
                "action": "meet",
                "person": "Anthony",
                "start_time": anthony_start_time,
                "end_time": anthony_end_time
            })
        else:
            itinerary.append({
                "action": "meet",
                "person": "Anthony",
                "start_time": anthony_start_time,
                "end_time": anthony_end_time
            })
            itinerary.append({
                "action": "meet",
                "person": "Laura",
                "start_time": laura_start_time,
                "end_time": laura_end_time
            })

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

solution = solve_scheduling_problem()
print(solution)