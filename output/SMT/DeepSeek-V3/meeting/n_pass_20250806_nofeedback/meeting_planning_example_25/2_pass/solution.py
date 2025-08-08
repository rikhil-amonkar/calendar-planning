from z3 import *

def solve_scheduling():
    # Create an Optimize instance for minimization
    opt = Optimize()

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
    # 1. Meeting must start >= david_start (4:00 PM)
    opt.add(start >= david_start)
    # 2. Meeting must end <= david_end (9:45 PM)
    opt.add(end <= david_end)
    # 3. Meeting duration is at least 105 minutes
    opt.add(end - start >= 105)
    # 4. Start time must be <= end time
    opt.add(start <= end)

    # To find the earliest possible meeting time, we minimize the start time
    opt.minimize(start)

    # Check if the solver can find a solution
    if opt.check() == sat:
        m = opt.model()
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