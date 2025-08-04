from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    # Stephanie's meeting in Financial District
    steph_start = Int('steph_start')
    steph_end = Int('steph_end')
    
    # John's meeting in Alamo Square
    john_start = Int('john_start')
    john_end = Int('john_end')

    # Convert all times to minutes since 9:00 AM (540 minutes in 24-hour time)
    # Stephanie's availability: 8:15 AM (495) to 11:30 AM (690)
    steph_available_start = 495 - 540  # 8:15 AM is 495 minutes in 24-hour time; relative to 9:00 AM (540)
    steph_available_end = 690 - 540    # 11:30 AM is 690 minutes

    # John's availability: 10:15 AM (615) to 8:45 PM (1245)
    john_available_start = 615 - 540   # 10:15 AM is 615 minutes
    john_available_end = 1245 - 540    # 8:45 PM is 1245 minutes

    # Meeting duration constraints
    s.add(steph_end - steph_start >= 90)  # At least 90 minutes with Stephanie
    s.add(john_end - john_start >= 30)    # At least 30 minutes with John

    # Meeting must be within their availability
    s.add(steph_start >= steph_available_start)
    s.add(steph_end <= steph_available_end)
    s.add(john_start >= john_available_start)
    s.add(john_end <= john_available_end)

    # Initial location: Embarcadero at time 0 (9:00 AM)
    # To meet Stephanie first:
    # Travel from Embarcadero to Financial District takes 5 minutes.
    s.add(steph_start >= 5)  # Can't start before arriving at Financial District at 9:05 AM

    # After meeting Stephanie, travel to Alamo Square to meet John:
    # Travel from Financial District to Alamo Square takes 17 minutes.
    s.add(john_start >= steph_end + 17)

    # Alternatively, meet John first:
    # Travel from Embarcadero to Alamo Square takes 19 minutes.
    # But John is only available from 10:15 AM (75 minutes after 9:00 AM)
    # So meeting John first would require:
    # john_start >= 19 (but also >= 75)
    # Then after meeting John, travel to Financial District to meet Stephanie:
    # Travel from Alamo Square to Financial District takes 17 minutes.
    # steph_start >= john_end + 17
    # But Stephanie is only available until 11:30 AM (150 minutes after 9:00 AM)
    # So meeting John first may not leave enough time for Stephanie's 90-minute meeting.

    # To maximize the number of friends met, we prioritize meeting both.
    # The solver will find feasible start and end times.

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        steph_start_val = m.eval(steph_start).as_long()
        steph_end_val = m.eval(steph_end).as_long()
        john_start_val = m.eval(john_start).as_long()
        john_end_val = m.eval(john_end).as_long()

        # Convert times back to HH:MM format
        def to_time_str(minutes):
            time = datetime.datetime(2023, 1, 1, 9, 0) + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        steph_start_time = to_time_str(steph_start_val)
        steph_end_time = to_time_str(steph_end_val)
        john_start_time = to_time_str(john_start_val)
        john_end_time = to_time_str(john_end_val)

        itinerary = [
            {"action": "meet", "person": "Stephanie", "start_time": steph_start_time, "end_time": steph_end_time},
            {"action": "meet", "person": "John", "start_time": john_start_time, "end_time": john_end_time}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(solution)