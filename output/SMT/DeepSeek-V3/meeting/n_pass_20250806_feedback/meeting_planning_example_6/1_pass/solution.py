from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the variables for the start and end times of the meeting with Kenneth
    start_hour = Int('start_hour')
    start_min = Int('start_min')
    end_hour = Int('end_hour')
    end_min = Int('end_min')

    # Constraints for Kenneth's availability (2:15 PM to 7:45 PM)
    s.add(start_hour >= 14)  # 2:15 PM is 14:15
    s.add(start_min >= 15)
    s.add(end_hour <= 19)    # 7:45 PM is 19:45
    s.add(end_min <= 45)

    # Meeting duration must be at least 90 minutes
    start_total = start_hour * 60 + start_min
    end_total = end_hour * 60 + end_min
    s.add(end_total - start_total >= 90)

    # Ensure the meeting starts and ends within Kenneth's availability
    s.add(start_total >= 14 * 60 + 15)  # 14:15
    s.add(end_total <= 19 * 60 + 45)    # 19:45

    # Ensure the start time is before the end time
    s.add(start_total < end_total)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        start_h = m.evaluate(start_hour).as_long()
        start_m = m.evaluate(start_min).as_long()
        end_h = m.evaluate(end_hour).as_long()
        end_m = m.evaluate(end_min).as_long()

        # Format the times to HH:MM
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_time = f"{end_h:02d}:{end_m:02d}"

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Kenneth",
                    "start_time": start_time,
                    "end_time": end_time
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve the problem and print the result
solution = solve_scheduling_problem()
print(solution)