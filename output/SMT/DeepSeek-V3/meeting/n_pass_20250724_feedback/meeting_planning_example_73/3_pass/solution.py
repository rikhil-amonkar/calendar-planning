from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()

    # Define variables for meeting start and end times (in minutes since midnight)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Convert all times to minutes since midnight
    my_arrival = 9 * 60  # 9:00 AM
    travel_time = 7  # minutes to Pacific Heights
    barbara_start = 7 * 60 + 15  # 7:15 AM
    barbara_end = 22 * 60  # 10:00 PM
    min_duration = 60  # minutes

    # Constraints
    # 1. Earliest possible meeting start is max(my arrival + travel, barbara's start)
    earliest_possible = If(my_arrival + travel_time > barbara_start,
                          my_arrival + travel_time,
                          barbara_start)
    solver.add(start_time >= earliest_possible)
    
    # 2. Meeting must end before barbara's availability ends
    solver.add(end_time <= barbara_end)
    
    # 3. Meeting duration is at least min_duration
    solver.add(end_time >= start_time + min_duration)
    
    # 4. Meeting must start after travel completes
    solver.add(start_time >= my_arrival + travel_time)

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start = model.eval(start_time).as_long()
        end = model.eval(end_time).as_long()

        # Convert minutes to HH:MM format
        start_str = (datetime.datetime.min + datetime.timedelta(minutes=start)).strftime("%H:%M")
        end_str = (datetime.datetime.min + datetime.timedelta(minutes=end)).strftime("%H:%M")

        # Return the itinerary
        return {
            "itinerary": [
                {"action": "meet", "person": "Barbara", "start_time": start_str, "end_time": end_str}
            ]
        }
    else:
        return {"itinerary": []}

# Run the solver and print the result
solution = solve_scheduling()
print(solution)