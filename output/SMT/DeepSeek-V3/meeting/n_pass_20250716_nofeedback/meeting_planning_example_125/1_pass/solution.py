from z3 import *
import json

def solve_scheduling_problem():
    # Create solver instance
    s = Solver()

    # Variables for meeting Stephanie
    meet_stephanie_start = Int('meet_stephanie_start')
    meet_stephanie_end = Int('meet_stephanie_end')

    # Variables for meeting John
    meet_john_start = Int('meet_john_start')
    meet_john_end = Int('meet_john_end')

    # Convert times to minutes since 9:00 AM (540 minutes since midnight)
    arrival_time = 9 * 60  # 9:00 AM in minutes
    stephanie_available_start = 8 * 60 + 15  # 8:15 AM in minutes
    stephanie_available_end = 11 * 60 + 30  # 11:30 AM in minutes
    john_available_start = 10 * 60 + 15  # 10:15 AM in minutes
    john_available_end = 20 * 60 + 45  # 8:45 PM in minutes

    # Constraints for meeting Stephanie
    s.add(meet_stephanie_start >= max(arrival_time, stephanie_available_start))
    s.add(meet_stephanie_end <= stephanie_available_end)
    s.add(meet_stephanie_end - meet_stephanie_start >= 90)  # 90 minutes meeting

    # Travel from Financial District (Stephanie) to Alamo Square (John) takes 17 minutes
    s.add(meet_john_start >= meet_stephanie_end + 17)

    # Constraints for meeting John
    s.add(meet_john_start >= john_available_start)
    s.add(meet_john_end <= john_available_end)
    s.add(meet_john_end - meet_john_start >= 30)  # 30 minutes meeting

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        steph_start = model.eval(meet_stephanie_start).as_long()
        steph_end = model.eval(meet_stephanie_end).as_long()
        john_start = model.eval(meet_john_start).as_long()
        john_end = model.eval(meet_john_end).as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        itinerary = [
            {"action": "meet", "person": "Stephanie", "start_time": minutes_to_time(steph_start), "end_time": minutes_to_time(steph_end)},
            {"action": "meet", "person": "John", "start_time": minutes_to_time(john_start), "end_time": minutes_to_time(john_end)}
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))