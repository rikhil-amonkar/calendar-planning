from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Meeting durations in minutes
    emily_min_duration = 105
    barbara_min_duration = 60
    william_min_duration = 105

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Available time windows (in minutes since midnight)
    emily_start = time_to_minutes("11:45")
    emily_end = time_to_minutes("15:15")
    barbara_start = time_to_minutes("16:45")
    barbara_end = time_to_minutes("18:15")
    william_start = time_to_minutes("17:15")
    william_end = time_to_minutes("19:00")

    # Travel times (in minutes)
    travel = {
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Chinatown"): 20,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Chinatown"): 16,
        ("Union Square", "Chinatown"): 7,
    }

    # Variables for meeting start and end times (in minutes since 9:00 AM)
    emily_meet_start = Int('emily_meet_start')
    emily_meet_end = Int('emily_meet_end')
    barbara_meet_start = Int('barbara_meet_start')
    barbara_meet_end = Int('barbara_meet_end')
    william_meet_start = Int('william_meet_start')
    william_meet_end = Int('william_meet_end')

    # Current location starts at The Castro at time 0 (9:00 AM)
    # We'll try to schedule all three meetings first

    # Emily's meeting constraints
    s.add(emily_meet_start >= 8)  # Travel to Alamo Square takes 8 minutes
    s.add(emily_meet_start >= emily_start - 540)
    s.add(emily_meet_end <= emily_end - 540)
    s.add(emily_meet_end - emily_meet_start >= emily_min_duration)

    # Barbara's meeting constraints
    s.add(barbara_meet_start >= barbara_start - 540)
    s.add(barbara_meet_end <= barbara_end - 540)
    s.add(barbara_meet_end - barbara_meet_start >= barbara_min_duration)

    # William's meeting constraints
    s.add(william_meet_start >= william_start - 540)
    s.add(william_meet_end <= william_end - 540)
    s.add(william_meet_end - william_meet_start >= william_min_duration)

    # Try scheduling in order: Emily -> Barbara -> William
    # Travel from Alamo Square to Union Square: 14 minutes
    s.add(barbara_meet_start >= emily_meet_end + 14)
    # Travel from Union Square to Chinatown: 7 minutes
    s.add(william_meet_start >= barbara_meet_end + 7)

    # Maximize the number of meetings (3 is the maximum)
    s.maximize(william_meet_end)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Emily's meeting
        em_start = m[emily_meet_start].as_long() + 540
        em_end = m[emily_meet_end].as_long() + 540
        itinerary.append({
            "action": "meet",
            "person": "Emily",
            "start_time": minutes_to_time(em_start),
            "end_time": minutes_to_time(em_end)
        })
        # Barbara's meeting
        ba_start = m[barbara_meet_start].as_long() + 540
        ba_end = m[barbara_meet_end].as_long() + 540
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": minutes_to_time(ba_start),
            "end_time": minutes_to_time(ba_end)
        })
        # William's meeting
        wi_start = m[william_meet_start].as_long() + 540
        wi_end = m[william_meet_end].as_long() + 540
        itinerary.append({
            "action": "meet",
            "person": "William",
            "start_time": minutes_to_time(wi_start),
            "end_time": minutes_to_time(wi_end)
        })
        return {"itinerary": itinerary}
    else:
        # If we can't schedule all three, try scheduling two meetings
        s = Optimize()
        
        # Try Emily and William
        s.add(emily_meet_start >= 8)  # Travel to Alamo Square
        s.add(emily_meet_start >= emily_start - 540)
        s.add(emily_meet_end <= emily_end - 540)
        s.add(emily_meet_end - emily_meet_start >= emily_min_duration)

        # Travel from Alamo Square to Chinatown: 16 minutes
        s.add(william_meet_start >= emily_meet_end + 16)
        s.add(william_meet_start >= william_start - 540)
        s.add(william_meet_end <= william_end - 540)
        s.add(william_meet_end - william_meet_start >= william_min_duration)

        s.maximize(william_meet_end)

        if s.check() == sat:
            m = s.model()
            itinerary = []
            # Emily's meeting
            em_start = m[emily_meet_start].as_long() + 540
            em_end = m[emily_meet_end].as_long() + 540
            itinerary.append({
                "action": "meet",
                "person": "Emily",
                "start_time": minutes_to_time(em_start),
                "end_time": minutes_to_time(em_end)
            })
            # William's meeting
            wi_start = m[william_meet_start].as_long() + 540
            wi_end = m[william_meet_end].as_long() + 540
            itinerary.append({
                "action": "meet",
                "person": "William",
                "start_time": minutes_to_time(wi_start),
                "end_time": minutes_to_time(wi_end)
            })
            return {"itinerary": itinerary}
        else:
            # Try Barbara and William
            s = Optimize()
            
            # Travel to Union Square: 19 minutes
            s.add(barbara_meet_start >= 19)
            s.add(barbara_meet_start >= barbara_start - 540)
            s.add(barbara_meet_end <= barbara_end - 540)
            s.add(barbara_meet_end - barbara_meet_start >= barbara_min_duration)

            # Travel from Union Square to Chinatown: 7 minutes
            s.add(william_meet_start >= barbara_meet_end + 7)
            s.add(william_meet_start >= william_start - 540)
            s.add(william_meet_end <= william_end - 540)
            s.add(william_meet_end - william_meet_start >= william_min_duration)

            s.maximize(william_meet_end)

            if s.check() == sat:
                m = s.model()
                itinerary = []
                # Barbara's meeting
                ba_start = m[barbara_meet_start].as_long() + 540
                ba_end = m[barbara_meet_end].as_long() + 540
                itinerary.append({
                    "action": "meet",
                    "person": "Barbara",
                    "start_time": minutes_to_time(ba_start),
                    "end_time": minutes_to_time(ba_end)
                })
                # William's meeting
                wi_start = m[william_meet_start].as_long() + 540
                wi_end = m[william_meet_end].as_long() + 540
                itinerary.append({
                    "action": "meet",
                    "person": "William",
                    "start_time": minutes_to_time(wi_start),
                    "end_time": minutes_to_time(wi_end)
                })
                return {"itinerary": itinerary}
            else:
                # If all else fails, return empty itinerary
                return {"itinerary": []}

result = solve_scheduling()
print(result)