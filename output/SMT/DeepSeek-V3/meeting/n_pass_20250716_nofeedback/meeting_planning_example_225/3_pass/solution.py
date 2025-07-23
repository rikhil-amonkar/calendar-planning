from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define time variables in minutes since 9:00 AM (540 minutes)
    # Meeting start and end times for each friend
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Convert friends' availability windows to minutes since 9:00 AM
    # Sarah: 4:00 PM to 6:15 PM (16:00 to 18:15) -> 960 to 1095 minutes
    sarah_available_start = 16 * 60 - 540  # 960 - 540 = 420
    sarah_available_end = (18 * 60 + 15) - 540  # 1095 - 540 = 555

    # Jeffrey: 3:00 PM to 10:00 PM (15:00 to 22:00) -> 900 to 1320 minutes
    jeffrey_available_start = 15 * 60 - 540  # 900 - 540 = 360
    jeffrey_available_end = 22 * 60 - 540  # 1320 - 540 = 780

    # Brian: 4:00 PM to 5:30 PM (16:00 to 17:30) -> 960 to 1050 minutes
    brian_available_start = 16 * 60 - 540  # 960 - 540 = 420
    brian_available_end = (17 * 60 + 30) - 540  # 1050 - 540 = 510

    # Meeting durations in minutes
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75

    # Add constraints for each meeting's duration and availability
    s.add(sarah_start >= sarah_available_start)
    s.add(sarah_end <= sarah_available_end)
    s.add(sarah_end == sarah_start + sarah_duration)

    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)
    s.add(jeffrey_end == jeffrey_start + jeffrey_duration)

    s.add(brian_start >= brian_available_start)
    s.add(brian_end <= brian_available_end)
    s.add(brian_end == brian_start + brian_duration)

    # Travel times between locations (in minutes)
    # Sunset to Union Square: 30
    # Union Square to North Beach: 10
    # North Beach to Alamo Square: 16

    # Assume initial location is Sunset District (arrival at 9:00 AM)
    # We'll try to meet Jeffrey first, then Sarah, then Brian
    s.add(jeffrey_start >= 30)  # travel from Sunset to Union Square
    s.add(sarah_start >= jeffrey_end + 10)  # travel from Union Square to North Beach
    s.add(brian_start >= sarah_end + 16)  # travel from North Beach to Alamo Square

    # Check if all meetings can fit
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Convert times back to HH:MM format (minutes since 9:00 AM)
        def to_time_str(minutes):
            total_minutes = 540 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        jeffrey_s = model.eval(jeffrey_start).as_long()
        jeffrey_e = model.eval(jeffrey_end).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Jeffrey",
            "start_time": to_time_str(jeffrey_s),
            "end_time": to_time_str(jeffrey_e)
        })

        sarah_s = model.eval(sarah_start).as_long()
        sarah_e = model.eval(sarah_end).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Sarah",
            "start_time": to_time_str(sarah_s),
            "end_time": to_time_str(sarah_e)
        })

        brian_s = model.eval(brian_start).as_long()
        brian_e = model.eval(brian_end).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Brian",
            "start_time": to_time_str(brian_s),
            "end_time": to_time_str(brian_e)
        })

        return {"itinerary": itinerary}
    else:
        # If meeting all three is not possible, try meeting two friends
        s.push()
        s.add(jeffrey_start >= 30)  # travel from Sunset to Union Square
        s.add(sarah_start >= jeffrey_end + 10)  # travel from Union Square to North Beach
        # Remove Brian's meeting constraints
        s.add(brian_start == -1)  # dummy, not meeting Brian
        s.add(brian_end == -1)
        if s.check() == sat:
            model = s.model()
            itinerary = []
            def to_time_str(minutes):
                total_minutes = 540 + minutes
                h = total_minutes // 60
                m = total_minutes % 60
                return f"{h:02d}:{m:02d}"

            jeffrey_s = model.eval(jeffrey_start).as_long()
            jeffrey_e = model.eval(jeffrey_end).as_long()
            itinerary.append({
                "action": "meet",
                "person": "Jeffrey",
                "start_time": to_time_str(jeffrey_s),
                "end_time": to_time_str(jeffrey_e)
            })

            sarah_s = model.eval(sarah_start).as_long()
            sarah_e = model.eval(sarah_end).as_long()
            itinerary.append({
                "action": "meet",
                "person": "Sarah",
                "start_time": to_time_str(sarah_s),
                "end_time": to_time_str(sarah_e)
            })

            s.pop()
            return {"itinerary": itinerary}
        s.pop()

        # Try meeting Jeffrey and Brian
        s.push()
        s.add(jeffrey_start >= 30)  # travel from Sunset to Union Square
        s.add(brian_start >= jeffrey_end + 15)  # travel from Union Square to Alamo Square
        s.add(sarah_start == -1)  # not meeting Sarah
        s.add(sarah_end == -1)
        if s.check() == sat:
            model = s.model()
            itinerary = []
            def to_time_str(minutes):
                total_minutes = 540 + minutes
                h = total_minutes // 60
                m = total_minutes % 60
                return f"{h:02d}:{m:02d}"

            jeffrey_s = model.eval(jeffrey_start).as_long()
            jeffrey_e = model.eval(jeffrey_end).as_long()
            itinerary.append({
                "action": "meet",
                "person": "Jeffrey",
                "start_time": to_time_str(jeffrey_s),
                "end_time": to_time_str(jeffrey_e)
            })

            brian_s = model.eval(brian_start).as_long()
            brian_e = model.eval(brian_end).as_long()
            itinerary.append({
                "action": "meet",
                "person": "Brian",
                "start_time": to_time_str(brian_s),
                "end_time": to_time_str(brian_e)
            })

            s.pop()
            return {"itinerary": itinerary}
        s.pop()

        # As a last resort, meet only Jeffrey
        s.push()
        s.add(jeffrey_start >= 30)
        s.add(jeffrey_end == jeffrey_start + jeffrey_duration)
        s.add(sarah_start == -1)
        s.add(sarah_end == -1)
        s.add(brian_start == -1)
        s.add(brian_end == -1)
        if s.check() == sat:
            model = s.model()
            itinerary = []
            def to_time_str(minutes):
                total_minutes = 540 + minutes
                h = total_minutes // 60
                m = total_minutes % 60
                return f"{h:02d}:{m:02d}"

            jeffrey_s = model.eval(jeffrey_start).as_long()
            jeffrey_e = model.eval(jeffrey_end).as_long()
            itinerary.append({
                "action": "meet",
                "person": "Jeffrey",
                "start_time": to_time_str(jeffrey_s),
                "end_time": to_time_str(jeffrey_e)
            })

            s.pop()
            return {"itinerary": itinerary}
        s.pop()

        # If all else fails, return empty itinerary
        return {"itinerary": []}

# Solve the problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))