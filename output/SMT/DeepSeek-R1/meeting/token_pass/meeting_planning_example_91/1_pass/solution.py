from z3 import *
import json

def main():
    # Convert all times to minutes from midnight
    start_time = 9 * 60  # 9:00 AM
    daniel_available_start = 19 * 60  # 19:00
    daniel_available_end = 20 * 60 + 15  # 20:15
    travel_to_richmond = 14  # minutes
    travel_back = 13  # minutes
    min_meeting_duration = 75  # minutes

    # Create solver
    solver = Optimize()

    # Variables
    leave_to_meet = Int('leave_to_meet')
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    leave_return = Int('leave_return')

    # Constraints
    solver.add(leave_to_meet >= start_time)
    solver.add(meeting_start == leave_to_meet + travel_to_richmond)
    solver.add(meeting_start >= daniel_available_start)
    solver.add(meeting_end == meeting_start + min_meeting_duration)
    solver.add(meeting_end <= daniel_available_end)
    solver.add(leave_return == meeting_end)
    solver.add(leave_return + travel_back >= 0)  # Placeholder for return if needed

    # Objective: maximize meeting duration (fixed here) and minimize waiting
    solver.maximize(meeting_start)  # Start meeting as early as possible to avoid conflicts

    if solver.check() == sat:
        model = solver.model()
        m_start = model.eval(meeting_start).as_long()
        m_end = model.eval(meeting_end).as_long()
        
        itinerary = [{
            "action": "meet",
            "location": "Richmond District",
            "person": "Daniel",
            "start_time": format_time(m_start),
            "end_time": format_time(m_end)
        }]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()