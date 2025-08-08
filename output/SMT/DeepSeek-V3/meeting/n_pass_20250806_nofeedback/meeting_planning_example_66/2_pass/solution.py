from z3 import *

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define variables for the start and end times of the meeting with Robert
    # Times are represented in minutes since 9:00 AM (540 minutes)
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Robert's availability: from 11:15 AM (135 minutes after 9:00 AM) to 5:45 PM (525 minutes after 9:00 AM)
    robert_start = 135  # 11:15 AM in minutes since 9:00 AM
    robert_end = 525    # 5:45 PM in minutes since 9:00 AM

    # Travel time from Nob Hill to Presidio is 17 minutes
    travel_time = 17

    # Constraints:
    # 1. You can leave Nob Hill no earlier than 9:00 AM (0 minutes after 9:00 AM)
    # 2. Arrival at Presidio is start_time - travel_time >= 0
    opt.add(start_time - travel_time >= 0)
    # 3. Meeting must start no earlier than Robert's availability
    opt.add(start_time >= robert_start)
    # 4. Meeting must end no later than Robert's availability
    opt.add(end_time <= robert_end)
    # 5. Meeting duration is at least 120 minutes
    opt.add(end_time - start_time >= 120)
    # 6. End time must be after start time
    opt.add(end_time > start_time)

    # Optimize for the earliest possible meeting to maximize flexibility
    opt.minimize(start_time)

    # Check if the problem is satisfiable
    if opt.check() == sat:
        m = opt.model()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        # Convert minutes since 9:00 AM to HH:MM format
        def to_time_str(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = to_time_str(start)
        end_str = to_time_str(end)

        # Create the itinerary
        itinerary = [
            {"action": "meet", "person": "Robert", "start_time": start_str, "end_time": end_str}
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Output the solution
solution = solve_scheduling_problem()
print(solution)