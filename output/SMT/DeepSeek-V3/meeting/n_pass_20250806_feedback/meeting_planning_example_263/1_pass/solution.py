from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    meet_karen_start = Int('meet_karen_start')
    meet_karen_end = Int('meet_karen_end')
    meet_anthony_start = Int('meet_anthony_start')
    meet_anthony_end = Int('meet_anthony_end')
    meet_betty_start = Int('meet_betty_start')
    meet_betty_end = Int('meet_betty_end')

    # Convert friend availability windows to minutes since 9:00 AM
    # Arrival time: 9:00 AM (0 minutes)
    karen_available_start = 45  # 8:45 AM is -15 minutes from 9:00 AM, but we start at 9:00 AM (0), so earliest is 0
    karen_available_end = 360   # 3:00 PM is 6 hours = 360 minutes
    anthony_available_start = 15  # 9:15 AM
    anthony_available_end = 750   # 9:30 PM is 12.5 hours = 750 minutes
    betty_available_start = 645   # 7:45 PM is 10.75 hours = 645 minutes
    betty_available_end = 825     # 9:45 PM is 12.75 hours = 765 minutes (but 7:45 PM to 9:45 PM is 2 hours = 120 minutes)

    # Minimum meeting durations (in minutes)
    min_karen = 30
    min_anthony = 105
    min_betty = 15

    # Add constraints for meeting durations
    s.add(meet_karen_end == meet_karen_start + min_karen)
    s.add(meet_anthony_end == meet_anthony_start + min_anthony)
    s.add(meet_betty_end == meet_betty_start + min_betty)

    # Add constraints for meeting within availability windows
    s.add(meet_karen_start >= karen_available_start)
    s.add(meet_karen_end <= karen_available_end)
    s.add(meet_anthony_start >= anthony_available_start)
    s.add(meet_anthony_end <= anthony_available_end)
    s.add(meet_betty_start >= betty_available_start)
    s.add(meet_betty_end <= betty_available_end)

    # Initial location is Bayview (starting at 9:00 AM)
    # We can choose the order of meetings. Let's assume the order is Karen -> Anthony -> Betty.
    # Add travel time constraints:
    # From Bayview to Fisherman's Wharf (Karen): 25 minutes
    s.add(meet_karen_start >= 25)  # Leave Bayview at 0, arrive at Fisherman's Wharf at 25

    # From Fisherman's Wharf to Financial District (Anthony): 11 minutes
    s.add(meet_anthony_start >= meet_karen_end + 11)

    # From Financial District to Embarcadero (Betty): 4 minutes
    s.add(meet_betty_start >= meet_anthony_end + 4)

    # Ensure no overlaps and order is maintained
    s.add(meet_karen_end <= meet_anthony_start)
    s.add(meet_anthony_end <= meet_betty_start)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format (starting from 9:00 AM)
        def minutes_to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours + 9:02d}:{mins:02d}"

        karen_start = m.eval(meet_karen_start).as_long()
        karen_end = m.eval(meet_karen_end).as_long()
        anthony_start = m.eval(meet_anthony_start).as_long()
        anthony_end = m.eval(meet_anthony_end).as_long()
        betty_start = m.eval(meet_betty_start).as_long()
        betty_end = m.eval(meet_betty_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_start), "end_time": minutes_to_time(karen_end)},
            {"action": "meet", "person": "Anthony", "start_time": minutes_to_time(anthony_start), "end_time": minutes_to_time(anthony_end)},
            {"action": "meet", "person": "Betty", "start_time": minutes_to_time(betty_start), "end_time": minutes_to_time(betty_end)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)