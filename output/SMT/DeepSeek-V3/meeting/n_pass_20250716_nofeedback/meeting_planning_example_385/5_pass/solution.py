from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define meeting variables (excluding Jeffrey)
    # John at Pacific Heights: 9:00 AM to 1:30 PM (until 810 minutes), min 15 minutes
    john_start = Int('john_start')
    john_end = Int('john_end')
    john_duration = 15

    # Steven at North Beach: 1:30 PM (810 minutes) to 10:00 PM (1320 minutes), min 45 minutes
    steven_start = Int('steven_start')
    steven_end = Int('steven_end')
    steven_duration = 45

    # Barbara at Fisherman's Wharf: 6:00 PM (1080 minutes) to 9:30 PM (1290 minutes), min 30 minutes
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    barbara_duration = 30

    # Convert all times to minutes since 9:00 AM (0 minutes is 9:00 AM)
    # John's window: 9:00 AM (0) to 1:30 PM (270)
    s.add(john_start >= 0)
    s.add(john_end <= 270)
    s.add(john_end - john_start >= john_duration)

    # Steven's window: 1:30 PM (810) to 10:00 PM (1320)
    s.add(steven_start >= 810)
    s.add(steven_end <= 1320)
    s.add(steven_end - steven_start >= steven_duration)

    # Barbara's window: 6:00 PM (1080) to 9:30 PM (1290)
    s.add(barbara_start >= 1080)
    s.add(barbara_end <= 1290)
    s.add(barbara_end - barbara_start >= barbara_duration)

    # Travel times (in minutes)
    # From Nob Hill to Pacific Heights: 8 minutes
    # From Pacific Heights to North Beach: 8 minutes
    # From North Beach to Fisherman's Wharf: 5 minutes

    # Sequence: John -> Steven -> Barbara
    # Start at Nob Hill at 0 minutes (9:00 AM)
    # Travel to Pacific Heights: 8 minutes
    s.add(john_start >= 8)
    s.add(john_end <= 270)

    # After meeting John, travel to North Beach: 8 minutes
    s.add(steven_start >= john_end + 8)
    s.add(steven_start >= 810)

    # After meeting Steven, travel to Fisherman's Wharf: 5 minutes
    s.add(barbara_start >= steven_end + 5)
    s.add(barbara_start >= 1080)

    if s.check() == sat:
        model = s.model()
        itinerary = []

        def to_time_str(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        # Add John's meeting
        john_s = model[john_start].as_long()
        john_e = model[john_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": to_time_str(john_s),
            "end_time": to_time_str(john_e)
        })

        # Add Steven's meeting
        steven_s = model[steven_start].as_long()
        steven_e = model[steven_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "Steven",
            "start_time": to_time_str(steven_s),
            "end_time": to_time_str(steven_e)
        })

        # Add Barbara's meeting
        barbara_s = model[barbara_start].as_long()
        barbara_e = model[barbara_end].as_long()
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": to_time_str(barbara_s),
            "end_time": to_time_str(barbara_e)
        })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))