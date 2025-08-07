from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Convert all times to minutes past 9:00 AM (540 minutes since midnight)
    # Variables:
    # meet_timothy_start, meet_timothy_end
    # meet_patricia_start, meet_patricia_end
    # meet_ashley_start, meet_ashley_end

    # Total available time: from 9:00 AM (0 minutes) to 9:45 PM (12*60 + 9*60 + 45 = 765 minutes)
    max_time = 765  # 9:45 PM is 765 minutes after 9:00 AM

    # Meeting durations in minutes
    timothy_min_duration = 120
    patricia_min_duration = 90
    ashley_min_duration = 45

    # Define variables
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')

    # Time windows for each friend (in minutes since 9:00 AM)
    # Patricia: 6:30 PM to 9:45 PM -> 9*60 + 30 = 570 to 765 minutes
    patricia_window_start = 570  # 6:30 PM is 570 minutes after 9:00 AM
    patricia_window_end = 765    # 9:45 PM is 765 minutes after 9:00 AM

    # Ashley: 8:30 PM to 9:15 PM -> 11*60 + 30 = 690 to 705 minutes
    ashley_window_start = 690    # 8:30 PM is 690 minutes after 9:00 AM
    ashley_window_end = 705      # 9:15 PM is 705 minutes after 9:00 AM

    # Timothy: 9:45 AM to 5:45 PM -> 45 to 8*60 + 45 = 525 minutes
    timothy_window_start = 45    # 9:45 AM is 45 minutes after 9:00 AM
    timothy_window_end = 525     # 5:45 PM is 525 minutes after 9:00 AM

    # Add constraints for each meeting
    # Timothy must be at Embarcadero
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(timothy_end == timothy_start + timothy_min_duration)

    # Patricia must be at Nob Hill
    s.add(patricia_start >= patricia_window_start)
    s.add(patricia_end <= patricia_window_end)
    s.add(patricia_end == patricia_start + patricia_min_duration)

    # Ashley must be at Mission District
    s.add(ashley_start >= ashley_window_start)
    s.add(ashley_end <= ashley_window_end)
    s.add(ashley_end == ashley_start + ashley_min_duration)

    # Initial location: Russian Hill at time 0 (9:00 AM)
    # Define variables to track location after each meeting
    # We need to model the sequence of meetings with travel times

    # We'll assume that we can meet Timothy, then possibly Ashley, then Patricia.
    # Alternatively, meet Ashley then Patricia (but not both if time doesn't permit).

    # Let's model the possible sequences and choose the one that allows meeting the most friends.

    # Option 1: Meet Timothy, then Ashley, then Patricia
    # Travel from Russian Hill to Embarcadero: 8 minutes
    s.add(timothy_start >= 8)  # travel time to Embarcadero

    # After meeting Timothy, travel to Mission District or Nob Hill for next meeting
    # To meet Ashley next: travel from Embarcadero to Mission District: 20 minutes
    # So ashley_start >= timothy_end + 20
    # Then, travel from Mission District to Nob Hill: 12 minutes
    # So patricia_start >= ashley_end + 12

    # Option 2: Meet Timothy, then Patricia (skipping Ashley)
    # Travel from Embarcadero to Nob Hill: 10 minutes
    # So patricia_start >= timothy_end + 10

    # Option 3: Meet Ashley, then Patricia (but starting from Russian Hill)
    # Travel from Russian Hill to Mission District: 16 minutes
    # ashley_start >= 16
    # Then travel from Mission District to Nob Hill: 12 minutes
    # patricia_start >= ashley_end + 12

    # But Ashley's window is very late, so this may not allow meeting Timothy.

    # Let's try to model meeting all three friends: Timothy, Ashley, Patricia
    meet_all = And(
        timothy_start >= 8,
        ashley_start >= timothy_end + 20,
        patricia_start >= ashley_end + 12,
        ashley_start >= ashley_window_start,
        ashley_end <= ashley_window_end,
        patricia_start >= patricia_window_start,
        patricia_end <= patricia_window_end
    )

    # Check if meeting all three is possible
    s.push()
    s.add(meet_all)
    if s.check() == sat:
        m = s.model()
        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(m[timothy_start].as_long()), "end_time": minutes_to_time(m[timothy_end].as_long())},
            {"action": "meet", "person": "Ashley", "start_time": minutes_to_time(m[ashley_start].as_long()), "end_time": minutes_to_time(m[ashley_end].as_long())},
            {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(m[patricia_start].as_long()), "end_time": minutes_to_time(m[patricia_end].as_long())}
        ]
        s.pop()
        return {"itinerary": itinerary}
    else:
        s.pop()

    # If meeting all three is not possible, try meeting Timothy and Patricia
    meet_timothy_patricia = And(
        timothy_start >= 8,
        patricia_start >= timothy_end + 10,
        patricia_start >= patricia_window_start,
        patricia_end <= patricia_window_end
    )
    s.push()
    s.add(meet_timothy_patricia)
    if s.check() == sat:
        m = s.model()
        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(m[timothy_start].as_long()), "end_time": minutes_to_time(m[timothy_end].as_long())},
            {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(m[patricia_start].as_long()), "end_time": minutes_to_time(m[patricia_end].as_long())}
        ]
        s.pop()
        return {"itinerary": itinerary}
    else:
        s.pop()

    # If that's not possible, try meeting Ashley and Patricia
    meet_ashley_patricia = And(
        ashley_start >= 16,
        patricia_start >= ashley_end + 12,
        ashley_start >= ashley_window_start,
        ashley_end <= ashley_window_end,
        patricia_start >= patricia_window_start,
        patricia_end <= patricia_window_end
    )
    s.push()
    s.add(meet_ashley_patricia)
    if s.check() == sat:
        m = s.model()
        itinerary = [
            {"action": "meet", "person": "Ashley", "start_time": minutes_to_time(m[ashley_start].as_long()), "end_time": minutes_to_time(m[ashley_end].as_long())},
            {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(m[patricia_start].as_long()), "end_time": minutes_to_time(m[patricia_end].as_long())}
        ]
        s.pop()
        return {"itinerary": itinerary}
    else:
        s.pop()

    # If nothing else, meet just Patricia
    meet_patricia = And(
        patricia_start >= patricia_window_start,
        patricia_end == patricia_start + patricia_min_duration,
        patricia_end <= patricia_window_end
    )
    s.push()
    s.add(meet_patricia)
    if s.check() == sat:
        m = s.model()
        itinerary = [
            {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(m[patricia_start].as_long()), "end_time": minutes_to_time(m[patricia_end].as_long())}
        ]
        s.pop()
        return {"itinerary": itinerary}
    else:
        s.pop()

    # Default: empty itinerary if no meetings can be scheduled
    return {"itinerary": []}

def minutes_to_time(minutes):
    # Convert minutes since 9:00 AM to HH:MM string
    total_minutes = 540 + minutes  # 9:00 AM is 540 minutes past midnight
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))