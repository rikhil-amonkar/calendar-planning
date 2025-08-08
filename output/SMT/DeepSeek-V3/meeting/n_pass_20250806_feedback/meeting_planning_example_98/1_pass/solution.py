from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define variables for the start and end times of meeting Timothy
    # We'll represent times as integers (minutes since 9:00AM)
    start_meet_timothy = Int('start_meet_timothy')
    end_meet_timothy = Int('end_meet_timothy')

    # Convert Timothy's availability to minutes since 9:00AM
    # 8:45PM is 11 hours and 45 minutes after 9:00AM (11*60 + 45 = 705 minutes)
    # 9:30PM is 12 hours and 30 minutes after 9:00AM (12*60 + 30 = 750 minutes)
    timothy_available_start = 705
    timothy_available_end = 750

    # Constraints for meeting Timothy
    # 1. Meeting must start within Timothy's availability
    s.add(start_meet_timothy >= timothy_available_start)
    s.add(start_meet_timothy <= timothy_available_end - 45)  # Ensure at least 45 minutes

    # 2. Meeting duration is at least 45 minutes
    s.add(end_meet_timothy == start_meet_timothy + 45)

    # 3. End time must be within Timothy's availability
    s.add(end_meet_timothy <= timothy_available_end)

    # 4. Travel time to Richmond District is 12 minutes
    # So we must leave Alamo Square at start_meet_timothy - 12
    departure_time = start_meet_timothy - 12
    s.add(departure_time >= 0)  # Can't leave before 9:00AM (0 minutes)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        start = model[start_meet_timothy].as_long()
        end = model[end_meet_timothy].as_long()

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_hours = 9 + minutes // 60
            total_minutes = minutes % 60
            return f"{total_hours:02d}:{total_minutes:02d}"

        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)

        # Create the itinerary
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "person": "Timothy",
                    "start_time": start_time,
                    "end_time": end_time
                }
            ]
        }
        return itinerary
    else:
        return {"itinerary": []}

# Solve and print the result
print(solve_scheduling())