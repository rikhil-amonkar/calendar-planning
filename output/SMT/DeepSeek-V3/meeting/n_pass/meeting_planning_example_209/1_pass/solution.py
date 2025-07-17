from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Melissa at North Beach: 8:15AM to 1:30PM, min 105 minutes (1.75 hours)
    melissa_start = Real('melissa_start')
    melissa_end = Real('melissa_end')

    # Anthony at Chinatown: 1:15PM to 2:30PM, min 60 minutes (1 hour)
    anthony_start = Real('anthony_start')
    anthony_end = Real('anthony_end')

    # Rebecca at Russian Hill: 7:30PM to 9:15PM, min 105 minutes (1.75 hours)
    rebecca_start = Real('rebecca_start')
    rebecca_end = Real('rebecca_end')

    # Convert all times to minutes since 9:00AM (540 minutes)
    # Constants for time windows in minutes since 9:00AM (0)
    # Melissa: 8:15AM to 1:30PM relative to 9:00AM is -45 to 270 minutes
    melissa_available_start = -45  # 8:15AM is 45 minutes before 9:00AM
    melissa_available_end = 270     # 1:30PM is 4.5 hours after 9:00AM (4.5*60=270)

    anthony_available_start = 255   # 1:15PM is 4.25 hours after 9:00AM (4.25*60=255)
    anthony_available_end = 330     # 2:30PM is 5.5 hours after 9:00AM (5.5*60=330)

    rebecca_available_start = 630   # 7:30PM is 10.5 hours after 9:00AM (10.5*60=630)
    rebecca_available_end = 735     # 9:15PM is 12.25 hours after 9:00AM (12.25*60=735)

    # Meeting duration constraints
    s.add(melissa_end - melissa_start >= 105)  # Melissa: 105 minutes
    s.add(anthony_end - anthony_start >= 60)   # Anthony: 60 minutes
    s.add(rebecca_end - rebecca_start >= 105)  # Rebecca: 105 minutes

    # Meeting must be within their available time windows
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)

    # Initial location: Sunset District at time 0 (9:00AM)
    # Travel times in minutes
    travel = {
        ('Sunset', 'North Beach'): 29,
        ('Sunset', 'Chinatown'): 30,
        ('Sunset', 'Russian Hill'): 24,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Sunset'): 27,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Sunset'): 29,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Sunset'): 23,
    }

    # Variables to track the order of meetings and locations
    # Assume the order is Melissa -> Anthony -> Rebecca
    # So, the path is Sunset -> North Beach -> Chinatown -> Russian Hill

    # Time to leave Sunset to North Beach: time 0 (9:00AM), travel 29 minutes
    arrive_north_beach = 0 + travel[('Sunset', 'North Beach')]
    s.add(melissa_start >= arrive_north_beach)

    # Time to leave North Beach to Chinatown: after Melissa meeting ends
    leave_north_beach = melissa_end
    arrive_chinatown = leave_north_beach + travel[('North Beach', 'Chinatown')]
    s.add(anthony_start >= arrive_chinatown)

    # Time to leave Chinatown to Russian Hill: after Anthony meeting ends
    leave_chinatown = anthony_end
    arrive_russian_hill = leave_chinatown + travel[('Chinatown', 'Russian Hill')]
    s.add(rebecca_start >= arrive_russian_hill)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Convert Real values to minutes and then to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = int(round(float(m[minutes].as_fraction())))
            # Since 0 is 9:00AM, handle negative times (Melissa starts before 9:00AM)
            base_hour = 9
            base_minute = 0
            total_minutes_since_midnight = base_hour * 60 + base_minute + total_minutes
            hours = (total_minutes_since_midnight // 60) % 24
            minutes = total_minutes_since_midnight % 60
            return f"{hours:02d}:{minutes:02d}"

        melissa_s = minutes_to_time(melissa_start)
        melissa_e = minutes_to_time(melissa_end)
        anthony_s = minutes_to_time(anthony_start)
        anthony_e = minutes_to_time(anthony_end)
        rebecca_s = minutes_to_time(rebecca_start)
        rebecca_e = minutes_to_time(rebecca_end)

        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": melissa_s, "end_time": melissa_e},
            {"action": "meet", "person": "Anthony", "start_time": anthony_s, "end_time": anthony_e},
            {"action": "meet", "person": "Rebecca", "start_time": rebecca_s, "end_time": rebecca_e}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute the solver
solution = solve_scheduling()
print(solution)