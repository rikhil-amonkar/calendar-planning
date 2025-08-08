from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Timothy at Embarcadero
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')

    # Meeting with Ashley at Mission District
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')

    # Meeting with Patricia at Nob Hill
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Constraints for Timothy (9:45 AM to 5:45 PM)
    s.add(timothy_start >= 45)  # 9:45 AM is 45 minutes after 9:00 AM
    s.add(timothy_end <= 525)   # 5:45 PM is 525 minutes after 9:00 AM
    s.add(timothy_end - timothy_start >= 120)  # Minimum 120 minutes

    # Constraints for Ashley (8:30 PM to 9:15 PM)
    ashley_available_start = 690  # 8:30 PM is 690 minutes after 9:00 AM
    ashley_available_end = 705    # 9:15 PM is 705 minutes after 9:00 AM
    s.add(ashley_start >= ashley_available_start)
    s.add(ashley_end <= ashley_available_end)
    s.add(ashley_end - ashley_start >= 45)  # Minimum 45 minutes

    # Constraints for Patricia (6:30 PM to 9:45 PM)
    patricia_available_start = 570  # 6:30 PM is 570 minutes after 9:00 AM
    patricia_available_end = 645    # 9:45 PM is 645 minutes after 9:00 AM
    s.add(patricia_start >= patricia_available_start)
    s.add(patricia_end <= patricia_available_end)
    s.add(patricia_end - patricia_start >= 90)  # Minimum 90 minutes

    # Initial location: Russian Hill at time 0 (9:00 AM)
    # Travel from Russian Hill to Embarcadero: 8 minutes
    s.add(timothy_start >= 8)  # arrive at Embarcadero by 9:08 AM
    s.add(timothy_start >= 45)  # but Timothy is available from 9:45 AM

    # After meeting Timothy, try going to Patricia first
    # Travel from Embarcadero to Nob Hill: 10 minutes
    s.add(patricia_start >= timothy_end + 10)

    # Then from Nob Hill to Mission District: 13 minutes
    s.add(ashley_start >= patricia_end + 13)

    # Check if this sequence works
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        timothy_start_time = minutes_to_time(m[timothy_start].as_long())
        timothy_end_time = minutes_to_time(m[timothy_end].as_long())
        patricia_start_time = minutes_to_time(m[patricia_start].as_long())
        patricia_end_time = minutes_to_time(m[patricia_end].as_long())
        ashley_start_time = minutes_to_time(m[ashley_start].as_long())
        ashley_end_time = minutes_to_time(m[ashley_end].as_long())

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": timothy_start_time, "end_time": timothy_end_time},
            {"action": "meet", "person": "Patricia", "start_time": patricia_start_time, "end_time": patricia_end_time},
            {"action": "meet", "person": "Ashley", "start_time": ashley_start_time, "end_time": ashley_end_time}
        ]
        return {"itinerary": itinerary}
    else:
        # Try alternative sequence: Timothy -> Ashley -> Patricia
        s.reset()
        s.add(timothy_start >= 45)
        s.add(timothy_end <= 525)
        s.add(timothy_end - timothy_start >= 120)
        s.add(ashley_start >= 690)
        s.add(ashley_end <= 705)
        s.add(ashley_end - ashley_start >= 45)
        s.add(patricia_start >= 570)
        s.add(patricia_end <= 645)
        s.add(patricia_end - patricia_start >= 90)

        # Travel from Russian Hill to Embarcadero: 8 minutes
        s.add(timothy_start >= 8)
        s.add(timothy_start >= 45)

        # After Timothy, go to Ashley first
        # Travel from Embarcadero to Mission District: 19 minutes
        s.add(ashley_start >= timothy_end + 19)

        # Then from Mission District to Nob Hill: 12 minutes
        s.add(patricia_start >= ashley_end + 12)

        if s.check() == sat:
            m = s.model()
            def minutes_to_time(minutes):
                total_minutes = 540 + minutes
                hours = total_minutes // 60
                mins = total_minutes % 60
                return f"{hours:02d}:{mins:02d}"

            timothy_start_time = minutes_to_time(m[timothy_start].as_long())
            timothy_end_time = minutes_to_time(m[timothy_end].as_long())
            ashley_start_time = minutes_to_time(m[ashley_start].as_long())
            ashley_end_time = minutes_to_time(m[ashley_end].as_long())
            patricia_start_time = minutes_to_time(m[patricia_start].as_long())
            patricia_end_time = minutes_to_time(m[patricia_end].as_long())

            itinerary = [
                {"action": "meet", "person": "Timothy", "start_time": timothy_start_time, "end_time": timothy_end_time},
                {"action": "meet", "person": "Ashley", "start_time": ashley_start_time, "end_time": ashley_end_time},
                {"action": "meet", "person": "Patricia", "start_time": patricia_start_time, "end_time": patricia_end_time}
            ]
            return {"itinerary": itinerary}
        else:
            # Try one more sequence: Meet Patricia first
            s.reset()
            s.add(timothy_start >= 45)
            s.add(timothy_end <= 525)
            s.add(timothy_end - timothy_start >= 120)
            s.add(ashley_start >= 690)
            s.add(ashley_end <= 705)
            s.add(ashley_end - ashley_start >= 45)
            s.add(patricia_start >= 570)
            s.add(patricia_end <= 645)
            s.add(patricia_end - patricia_start >= 90)

            # Travel from Russian Hill to Nob Hill: 5 minutes
            s.add(patricia_start >= 5)
            s.add(patricia_start >= 570)  # Patricia available from 6:30 PM

            # After Patricia, go to Timothy
            # Travel from Nob Hill to Embarcadero: 9 minutes
            s.add(timothy_start >= patricia_end + 9)

            # Then from Embarcadero to Mission District: 19 minutes
            s.add(ashley_start >= timothy_end + 19)

            if s.check() == sat:
                m = s.model()
                def minutes_to_time(minutes):
                    total_minutes = 540 + minutes
                    hours = total_minutes // 60
                    mins = total_minutes % 60
                    return f"{hours:02d}:{mins:02d}"

                patricia_start_time = minutes_to_time(m[patricia_start].as_long())
                patricia_end_time = minutes_to_time(m[patricia_end].as_long())
                timothy_start_time = minutes_to_time(m[timothy_start].as_long())
                timothy_end_time = minutes_to_time(m[timothy_end].as_long())
                ashley_start_time = minutes_to_time(m[ashley_start].as_long())
                ashley_end_time = minutes_to_time(m[ashley_end].as_long())

                itinerary = [
                    {"action": "meet", "person": "Patricia", "start_time": patricia_start_time, "end_time": patricia_end_time},
                    {"action": "meet", "person": "Timothy", "start_time": timothy_start_time, "end_time": timothy_end_time},
                    {"action": "meet", "person": "Ashley", "start_time": ashley_start_time, "end_time": ashley_end_time}
                ]
                return {"itinerary": itinerary}
            else:
                return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))