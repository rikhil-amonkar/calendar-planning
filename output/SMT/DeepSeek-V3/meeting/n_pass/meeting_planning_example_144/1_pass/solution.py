from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting Laura in Mission District
    laura_start = Int('laura_start')
    laura_end = Int('laura_end')
    # Meeting Anthony in Financial District
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    laura_available_start = 12 * 60 + 15  # 12:15 PM in minutes
    laura_available_end = 19 * 60 + 45    # 19:45 PM in minutes
    anthony_available_start = 12 * 60 + 30  # 12:30 PM in minutes
    anthony_available_end = 14 * 60 + 45    # 14:45 PM in minutes

    # Add constraints for Laura's meeting
    s.add(laura_start >= laura_available_start)
    s.add(laura_end <= laura_available_end)
    s.add(laura_end - laura_start >= 75)  # 75 minutes minimum

    # Add constraints for Anthony's meeting
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end - anthony_start >= 30)  # 30 minutes minimum

    # Possible schedules: meet Laura first or Anthony first
    # We need to model the travel times between locations

    # Scenario 1: Meet Anthony first, then Laura
    # Travel from Castro to Financial District: 20 minutes
    # Then from Financial District to Mission District: 17 minutes
    scenario1 = And(
        anthony_start >= 540 + 20,  # 9:00 AM + 20 minutes travel
        laura_start >= anthony_end + 17  # Travel from Financial to Mission
    )

    # Scenario 2: Meet Laura first, then Anthony
    # Travel from Castro to Mission District: 7 minutes
    # Then from Mission District to Financial District: 17 minutes
    scenario2 = And(
        laura_start >= 540 + 7,  # 9:00 AM + 7 minutes travel
        anthony_start >= laura_end + 17  # Travel from Mission to Financial
    )

    # Add either scenario1 or scenario2 to the solver
    s.add(Or(scenario1, scenario2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Extract the times
        laura_s = m.evaluate(laura_start).as_long()
        laura_e = m.evaluate(laura_end).as_long()
        anthony_s = m.evaluate(anthony_start).as_long()
        anthony_e = m.evaluate(anthony_end).as_long()

        # Convert minutes back to HH:MM format
        def to_time_str(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        itinerary = []
        # Determine the order of meetings based on start times
        if anthony_s < laura_s:
            itinerary.append({
                "action": "meet",
                "person": "Anthony",
                "start_time": to_time_str(anthony_s),
                "end_time": to_time_str(anthony_e)
            })
            itinerary.append({
                "action": "meet",
                "person": "Laura",
                "start_time": to_time_str(laura_s),
                "end_time": to_time_str(laura_e)
            })
        else:
            itinerary.append({
                "action": "meet",
                "person": "Laura",
                "start_time": to_time_str(laura_s),
                "end_time": to_time_str(laura_e)
            })
            itinerary.append({
                "action": "meet",
                "person": "Anthony",
                "start_time": to_time_str(anthony_s),
                "end_time": to_time_str(anthony_e)
            })

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute the solver
solution = solve_scheduling()
print(solution)