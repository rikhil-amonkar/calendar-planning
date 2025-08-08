from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for the start and end times of the meeting with David (in minutes since 9:00 AM)
    start = Int('start')
    end = Int('end')

    # Convert time constraints to minutes since 9:00 AM
    # David is available from 4:00 PM (which is 7 * 60 = 420 minutes since 9:00 AM) to 9:45 PM (12 * 60 + 45 = 765 minutes since 9:00 AM)
    david_start = 420  # 4:00 PM
    david_end = 765    # 9:45 PM

    # Travel time to Chinatown is 23 minutes
    travel_time = 23

    # Constraints:
    # 1. You can't start meeting before arriving at Chinatown (arrival at Chinatown is at least 9:00 AM + 23 minutes = 9:23 AM)
    #    But since David is only available from 4:00 PM, this constraint is automatically satisfied.
    # 2. Meeting must start >= david_start (4:00 PM)
    s.add(start >= david_start)
    # 3. Meeting must end <= david_end (9:45 PM)
    s.add(end <= david_end)
    # 4. Meeting duration is at least 105 minutes
    s.add(end - start >= 105)
    # 5. Start time must be <= end time
    s.add(start <= end)

    # To find the earliest possible meeting time, we minimize the start time
    s.minimize(start)

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        start_time = m[start].as_long()
        end_time = m[end].as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)

        # Prepare the itinerary
        itinerary = {
            "itinerary": [
                {"action": "meet", "person": "David", "start_time": start_str, "end_time": end_str}
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve and print the result
print(solve_scheduling())