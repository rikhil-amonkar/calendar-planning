from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Betty's availability: 10:15 AM (615) to 9:30 PM (1290)
    betty_start_min = 615
    betty_end_min = 1290
    # David's availability: 1:00 PM (780) to 8:15 PM (1215)
    david_start_min = 780
    david_end_min = 1215
    # Barbara's availability: 9:15 AM (555) to 8:15 PM (1215)
    barbara_start_min = 555
    barbara_end_min = 1215

    # Meeting durations in minutes
    betty_duration = 45
    david_duration = 90
    barbara_duration = 120

    # Define variables for meeting start times (in minutes since 9:00 AM)
    betty_start = Int('betty_start')
    david_start = Int('david_start')
    barbara_start = Int('barbara_start')

    # Define meeting end times
    betty_end = betty_start + betty_duration
    david_end = david_start + david_duration
    barbara_end = barbara_start + barbara_duration

    # Constraints for meeting within availability windows
    s.add(betty_start >= betty_start_min)
    s.add(betty_end <= betty_end_min)
    s.add(david_start >= david_start_min)
    s.add(david_end <= david_end_min)
    s.add(barbara_start >= barbara_start_min)
    s.add(barbara_end <= barbara_end_min)

    # Initial location is Embarcadero at time 0 (9:00 AM)
    # Barbara is at Fisherman's Wharf (6 minutes from Embarcadero)
    # Betty is at Presidio (20 minutes from Embarcadero)
    # David is at Richmond District (21 minutes from Embarcadero)

    # Define the order of meetings. We need to model the sequence of meetings and travel times.
    # We'll use a variable to represent the order, but for simplicity, let's assume a fixed order and check feasibility.
    # Alternatively, we can model all possible permutations of meetings (3! = 6 possibilities).

    # We'll try different orders and pick the feasible one.

    # Let's try the order: Barbara -> Betty -> David
    s.push()
    s.add(barbara_start >= 540 + 6)  # Travel to Barbara takes 6 minutes
    s.add(betty_start >= barbara_end + travel_time('Fisherman\'s Wharf', 'Presidio'))
    s.add(david_start >= betty_end + travel_time('Presidio', 'Richmond District'))
    if s.check() == sat:
        m = s.model()
        itinerary = []
        barbara_start_time = m[barbara_start].as_long()
        betty_start_time = m[betty_start].as_long()
        david_start_time = m[david_start].as_long()
        itinerary.append(create_meeting_entry("Barbara", barbara_start_time))
        itinerary.append(create_meeting_entry("Betty", betty_start_time))
        itinerary.append(create_meeting_entry("David", david_start_time))
        s.pop()
        return {"itinerary": itinerary}

    s.pop()

    # Try order: Barbara -> David -> Betty
    s.push()
    s.add(barbara_start >= 540 + 6)  # Travel to Barbara
    s.add(david_start >= barbara_end + travel_time('Fisherman\'s Wharf', 'Richmond District'))
    s.add(betty_start >= david_end + travel_time('Richmond District', 'Presidio'))
    if s.check() == sat:
        m = s.model()
        itinerary = []
        barbara_start_time = m[barbara_start].as_long()
        david_start_time = m[david_start].as_long()
        betty_start_time = m[betty_start].as_long()
        itinerary.append(create_meeting_entry("Barbara", barbara_start_time))
        itinerary.append(create_meeting_entry("David", david_start_time))
        itinerary.append(create_meeting_entry("Betty", betty_start_time))
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # Try order: Betty -> Barbara -> David
    s.push()
    s.add(betty_start >= 540 + 20)  # Travel to Betty
    s.add(barbara_start >= betty_end + travel_time('Presidio', 'Fisherman\'s Wharf'))
    s.add(david_start >= barbara_end + travel_time('Fisherman\'s Wharf', 'Richmond District'))
    if s.check() == sat:
        m = s.model()
        itinerary = []
        betty_start_time = m[betty_start].as_long()
        barbara_start_time = m[barbara_start].as_long()
        david_start_time = m[david_start].as_long()
        itinerary.append(create_meeting_entry("Betty", betty_start_time))
        itinerary.append(create_meeting_entry("Barbara", barbara_start_time))
        itinerary.append(create_meeting_entry("David", david_start_time))
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # Try order: Betty -> David -> Barbara
    s.push()
    s.add(betty_start >= 540 + 20)
    s.add(david_start >= betty_end + travel_time('Presidio', 'Richmond District'))
    s.add(barbara_start >= david_end + travel_time('Richmond District', 'Fisherman\'s Wharf'))
    if s.check() == sat:
        m = s.model()
        itinerary = []
        betty_start_time = m[betty_start].as_long()
        david_start_time = m[david_start].as_long()
        barbara_start_time = m[barbara_start].as_long()
        itinerary.append(create_meeting_entry("Betty", betty_start_time))
        itinerary.append(create_meeting_entry("David", david_start_time))
        itinerary.append(create_meeting_entry("Barbara", barbara_start_time))
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # Try order: David -> Barbara -> Betty
    s.push()
    s.add(david_start >= 540 + 21)  # Travel to David
    s.add(barbara_start >= david_end + travel_time('Richmond District', 'Fisherman\'s Wharf'))
    s.add(betty_start >= barbara_end + travel_time('Fisherman\'s Wharf', 'Presidio'))
    if s.check() == sat:
        m = s.model()
        itinerary = []
        david_start_time = m[david_start].as_long()
        barbara_start_time = m[barbara_start].as_long()
        betty_start_time = m[betty_start].as_long()
        itinerary.append(create_meeting_entry("David", david_start_time))
        itinerary.append(create_meeting_entry("Barbara", barbara_start_time))
        itinerary.append(create_meeting_entry("Betty", betty_start_time))
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # Try order: David -> Betty -> Barbara
    s.push()
    s.add(david_start >= 540 + 21)
    s.add(betty_start >= david_end + travel_time('Richmond District', 'Presidio'))
    s.add(barbara_start >= betty_end + travel_time('Presidio', 'Fisherman\'s Wharf'))
    if s.check() == sat:
        m = s.model()
        itinerary = []
        david_start_time = m[david_start].as_long()
        betty_start_time = m[betty_start].as_long()
        barbara_start_time = m[barbara_start].as_long()
        itinerary.append(create_meeting_entry("David", david_start_time))
        itinerary.append(create_meeting_entry("Betty", betty_start_time))
        itinerary.append(create_meeting_entry("Barbara", barbara_start_time))
        s.pop()
        return {"itinerary": itinerary}
    s.pop()

    # If none of the above orders work, return an empty itinerary
    return {"itinerary": []}

def travel_time(from_loc, to_loc):
    # Travel times in minutes
    travel_times = {
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18
    }
    return travel_times[(from_loc, to_loc)]

def create_meeting_entry(person, start_time_minutes):
    # Convert minutes since 9:00 AM to HH:MM format
    total_minutes = start_time_minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"

    if person == "Betty":
        end_time_minutes = start_time_minutes + 45
    elif person == "David":
        end_time_minutes = start_time_minutes + 90
    elif person == "Barbara":
        end_time_minutes = start_time_minutes + 120

    end_hours = end_time_minutes // 60
    end_minutes = end_time_minutes % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"

    return {"action": "meet", "person": person, "start_time": start_time, "end_time": end_time}

# Solve the problem
solution = solve_scheduling()
print(solution)