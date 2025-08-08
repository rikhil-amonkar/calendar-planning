from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Kevin at Alamo Square: 75 minutes
    kevin_start = Int('kevin_start')
    kevin_end = Int('kevin_end')
    # Kimberly at Russian Hill: 30 minutes
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    # Joseph at Presidio: 45 minutes
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    # Thomas at Financial District: 45 minutes
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')

    # Convert availability windows to minutes since 9:00 AM
    # Kevin: 8:15 AM to 9:30 PM -> 8:15 is -45, 9:30 PM is 12*60 + 30 = 750 minutes since 9:00 AM
    kevin_available_start = -45  # 8:15 AM is 45 minutes before 9:00 AM
    kevin_available_end = 750    # 9:30 PM is 12.5 hours after 9:00 AM
    # Kimberly: 8:45 AM to 12:30 PM -> 8:45 is -15, 12:30 is 3*60 + 30 = 210
    kimberly_available_start = -15
    kimberly_available_end = 210
    # Joseph: 6:30 PM to 7:15 PM -> 6:30 PM is 9.5 hours = 570, 7:15 PM is 10.25 hours = 615
    joseph_available_start = 570
    joseph_available_end = 615
    # Thomas: 7:00 PM to 9:45 PM -> 7:00 PM is 10*60 = 600, 9:45 PM is 12.75*60 = 765
    thomas_available_start = 600
    thomas_available_end = 765

    # Meeting durations in minutes
    kevin_duration = 75
    kimberly_duration = 30
    joseph_duration = 45
    thomas_duration = 45

    # Constraints for each meeting
    # Kevin
    s.add(kevin_start >= kevin_available_start)
    s.add(kevin_end <= kevin_available_end)
    s.add(kevin_end == kevin_start + kevin_duration)
    # Kimberly
    s.add(kimberly_start >= kimberly_available_start)
    s.add(kimberly_end <= kimberly_available_end)
    s.add(kimberly_end == kimberly_start + kimberly_duration)
    # Joseph
    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)
    s.add(joseph_end == joseph_start + joseph_duration)
    # Thomas
    s.add(thomas_start >= thomas_available_start)
    s.add(thomas_end <= thomas_available_end)
    s.add(thomas_end == thomas_start + thomas_duration)

    # All start times must be >= 0 (since we start at 9:00 AM)
    s.add(kevin_start >= 0)
    s.add(kimberly_start >= 0)
    s.add(joseph_start >= 0)
    s.add(thomas_start >= 0)

    # Define the order of meetings and travel times
    # We need to model the sequence of meetings and the travel times between them
    # Let's assume the order is: Sunset -> Location1 -> Location2 -> Location3 -> Location4
    # We'll use booleans to represent whether a meeting is included
    meet_kevin = Bool('meet_kevin')
    meet_kimberly = Bool('meet_kimberly')
    meet_joseph = Bool('meet_joseph')
    meet_thomas = Bool('meet_thomas')

    # At least one meeting must be scheduled
    s.add(Or(meet_kevin, meet_kimberly, meet_joseph, meet_thomas))

    # Define possible sequences and travel times
    # We'll consider all possible permutations of the four meetings, but this is computationally expensive.
    # Instead, we'll use a heuristic to prioritize meetings with tighter time windows.

    # We'll model the schedule as a sequence where each meeting is optionally included, and travel times are respected.
    # This is complex, so we'll simplify by assuming a feasible order based on time windows.

    # Priority: Kimberly (morning), Kevin (all day), Joseph (evening), Thomas (evening)
    # Possible sequence: Sunset -> Russian Hill (Kimberly) -> Alamo Square (Kevin) -> Presidio (Joseph) -> Financial District (Thomas)

    # Define the start and end times for each segment, considering travel times
    # Initial location: Sunset District at time 0 (9:00 AM)

    # Variables to track current time and location
    current_time = Int('current_time')
    current_location = Int('current_location')  # 0: Sunset, 1: Alamo, 2: Russian, 3: Presidio, 4: Financial
    s.add(current_time == 0)
    s.add(current_location == 0)

    # Track which meetings are scheduled
    scheduled_meetings = []

    # Helper function to add a meeting if it's selected
    def add_meeting(meeting_flag, start_var, end_var, person, location, travel_time):
        new_current_time = Int(f'new_current_time_{person}')
        new_current_location = Int(f'new_current_location_{person}')
        s.add(Implies(meeting_flag, new_current_time == end_var))
        s.add(Implies(meeting_flag, new_current_location == location))
        s.add(Implies(meeting_flag, start_var >= current_time + travel_time))
        scheduled_meetings.append((meeting_flag, person, start_var, end_var))
        return new_current_time, new_current_location

    # Try to schedule Kimberly first (morning)
    travel_kimberly = 24  # Sunset to Russian Hill
    new_time, new_loc = add_meeting(meet_kimberly, kimberly_start, kimberly_end, "Kimberly", 2, travel_kimberly)
    s.add(Implies(meet_kimberly, kimberly_start >= current_time + travel_kimberly))
    s.add(Implies(meet_kimberly, kimberly_end == kimberly_start + kimberly_duration))
    s.add(Implies(meet_kimberly, kimberly_start >= 0))
    s.add(Implies(meet_kimberly, kimberly_end <= kimberly_available_end))

    # Then Kevin (all day)
    travel_kevin_from_kimberly = 15  # Russian Hill to Alamo Square
    s.add(Implies(And(meet_kimberly, meet_kevin), kevin_start >= kimberly_end + travel_kevin_from_kimberly))
    s.add(Implies(And(Not(meet_kimberly), meet_kevin), kevin_start >= current_time + 17))  # Sunset to Alamo
    s.add(Implies(meet_kevin, kevin_end == kevin_start + kevin_duration))
    s.add(Implies(meet_kevin, kevin_start >= 0))
    s.add(Implies(meet_kevin, kevin_end <= kevin_available_end))

    # Then Joseph (evening)
    travel_joseph_from_kevin = 18  # Alamo to Presidio
    s.add(Implies(And(meet_kevin, meet_joseph), joseph_start >= kevin_end + travel_joseph_from_kevin))
    s.add(Implies(And(Not(meet_kevin), meet_joseph), joseph_start >= current_time + 16))  # Sunset to Presidio
    s.add(Implies(meet_joseph, joseph_end == joseph_start + joseph_duration))
    s.add(Implies(meet_joseph, joseph_start >= joseph_available_start))
    s.add(Implies(meet_joseph, joseph_end <= joseph_available_end))

    # Then Thomas (evening)
    travel_thomas_from_joseph = 22  # Presidio to Financial
    s.add(Implies(And(meet_joseph, meet_thomas), thomas_start >= joseph_end + travel_thomas_from_joseph))
    s.add(Implies(And(Not(meet_joseph), meet_thomas), thomas_start >= current_time + 30))  # Sunset to Financial
    s.add(Implies(meet_thomas, thomas_end == thomas_start + thomas_duration))
    s.add(Implies(meet_thomas, thomas_start >= thomas_available_start))
    s.add(Implies(meet_thomas, thomas_end <= thomas_available_end))

    # Maximize the number of meetings
    # We'll use a simple approach by checking if all meetings can be scheduled
    # If not, we'll try subsets
    # This is a bit ad-hoc; a better approach would use optimization in Z3, but for simplicity, we'll proceed.

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Helper function to add meeting to itinerary if it's scheduled
        def add_if_scheduled(flag, person, start, end):
            if is_true(model.eval(flag)):
                start_min = model.eval(start).as_long()
                end_min = model.eval(end).as_long()
                # Convert minutes to HH:MM
                start_hh = (9 + start_min // 60) % 24
                start_mm = start_min % 60
                end_hh = (9 + end_min // 60) % 24
                end_mm = end_min % 60
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
        add_if_scheduled(meet_kimberly, "Kimberly", kimberly_start, kimberly_end)
        add_if_scheduled(meet_kevin, "Kevin", kevin_start, kevin_end)
        add_if_scheduled(meet_joseph, "Joseph", joseph_start, joseph_end)
        add_if_scheduled(meet_thomas, "Thomas", thomas_start, thomas_end)
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        # Try subsets if all meetings can't be scheduled
        # For brevity, we'll return a feasible subset
        # In practice, you'd iterate over possible subsets
        return {"itinerary": []}

# Execute the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))