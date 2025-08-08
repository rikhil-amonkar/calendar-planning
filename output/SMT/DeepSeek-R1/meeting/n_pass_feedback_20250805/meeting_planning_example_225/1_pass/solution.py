from z3 import *

# Travel times between locations (in minutes)
travel_times = {
    ("Sunset", "North"): 29,
    ("Sunset", "Union"): 30,
    ("Sunset", "Alamo"): 17,
    ("North", "Sunset"): 27,
    ("North", "Union"): 7,
    ("North", "Alamo"): 16,
    ("Union", "Sunset"): 26,
    ("Union", "North"): 10,
    ("Union", "Alamo"): 15,
    ("Alamo", "Sunset"): 16,
    ("Alamo", "North"): 15,
    ("Alamo", "Union"): 14,
}

# Meeting details: location, duration, available start and end times (in minutes from 9:00 AM)
meetings = {
    "Jeffrey": {
        "location": "Union",
        "duration": 75,
        "available_start": 360,  # 15:00 (3:00 PM)
        "available_end": 705     # 20:45 (8:45 PM) = 22:00 - 75 minutes
    },
    "Sarah": {
        "location": "North",
        "duration": 60,
        "available_start": 420,  # 16:00 (4:00 PM)
        "available_end": 495     # 17:15 (5:15 PM) = 18:15 - 60 minutes
    },
    "Brian": {
        "location": "Alamo",
        "duration": 75,
        "available_start": 420,  # 16:00 (4:00 PM)
        "available_end": 435     # 16:15 (4:15 PM) = 17:30 - 75 minutes
    }
}

def minutes_to_time(minutes):
    """Convert minutes from 9:00 AM to HH:MM format."""
    total_minutes = int(minutes)
    hours = total_minutes // 60
    minutes_remainder = total_minutes % 60
    total_hour = 9 + hours
    return f"{total_hour:02d}:{minutes_remainder:02d}"

def schedule_pair(meeting1, meeting2):
    """Schedule two meetings considering both possible orders."""
    s = Solver()
    a_start = Int(f'{meeting1}_start')
    b_start = Int(f'{meeting2}_start')
    m1 = meetings[meeting1]
    m2 = meetings[meeting2]
    
    # Option 1: meeting1 then meeting2
    option1 = And(
        a_start >= travel_times[("Sunset", m1["location"])],
        a_start >= m1["available_start"],
        a_start <= m1["available_end"],
        b_start >= a_start + m1["duration"] + travel_times[(m1["location"], m2["location"])],
        b_start >= m2["available_start"],
        b_start <= m2["available_end"]
    )
    
    # Option 2: meeting2 then meeting1
    option2 = And(
        b_start >= travel_times[("Sunset", m2["location"])],
        b_start >= m2["available_start"],
        b_start <= m2["available_end"],
        a_start >= b_start + m2["duration"] + travel_times[(m2["location"], m1["location"])],
        a_start >= m1["available_start"],
        a_start <= m1["available_end"]
    )
    
    s.add(Or(option1, option2))
    if s.check() == sat:
        model = s.model()
        a_val = model[a_start].as_long()
        b_val = model[b_start].as_long()
        meeting1_entry = {
            "action": "meet",
            "person": meeting1,
            "start_time": minutes_to_time(a_val),
            "end_time": minutes_to_time(a_val + m1["duration"])
        }
        meeting2_entry = {
            "action": "meet",
            "person": meeting2,
            "start_time": minutes_to_time(b_val),
            "end_time": minutes_to_time(b_val + m2["duration"])
        }
        return [meeting1_entry, meeting2_entry]
    else:
        return None

def schedule_one(meeting):
    """Schedule a single meeting."""
    s = Solver()
    a_start = Int(f'{meeting}_start')
    m = meetings[meeting]
    s.add(a_start >= travel_times[("Sunset", m["location"])])
    s.add(a_start >= m["available_start"])
    s.add(a_start <= m["available_end"])
    if s.check() == sat:
        model = s.model()
        a_val = model[a_start].as_long()
        return [{
            "action": "meet",
            "person": meeting,
            "start_time": minutes_to_time(a_val),
            "end_time": minutes_to_time(a_val + m["duration"])
        }]
    else:
        return None

def main():
    # Try to schedule all three meetings
    j_start = Int('Jeffrey_start')
    s_start = Int('Sarah_start')
    b_start = Int('Brian_start')
    s = Solver()
    
    # Constraints for all three meetings
    constraints = [
        j_start >= travel_times[("Sunset", "Union")],
        s_start >= travel_times[("Sunset", "North")],
        b_start >= travel_times[("Sunset", "Alamo")],
        j_start >= meetings["Jeffrey"]["available_start"],
        j_start <= meetings["Jeffrey"]["available_end"],
        s_start >= meetings["Sarah"]["available_start"],
        s_start <= meetings["Sarah"]["available_end"],
        b_start >= meetings["Brian"]["available_start"],
        b_start <= meetings["Brian"]["available_end"],
        Or(
            j_start + meetings["Jeffrey"]["duration"] + travel_times[("Union", "North")] <= s_start,
            s_start + meetings["Sarah"]["duration"] + travel_times[("North", "Union")] <= j_start
        ),
        Or(
            j_start + meetings["Jeffrey"]["duration"] + travel_times[("Union", "Alamo")] <= b_start,
            b_start + meetings["Brian"]["duration"] + travel_times[("Alamo", "Union")] <= j_start
        ),
        Or(
            s_start + meetings["Sarah"]["duration"] + travel_times[("North", "Alamo")] <= b_start,
            b_start + meetings["Brian"]["duration"] + travel_times[("Alamo", "North")] <= s_start
        )
    ]
    s.add(constraints)
    if s.check() == sat:
        model = s.model()
        j_val = model[j_start].as_long()
        s_val = model[s_start].as_long()
        b_val = model[b_start].as_long()
        list_with_val = [
            (j_val, {
                "action": "meet", 
                "person": "Jeffrey", 
                "start_time": minutes_to_time(j_val), 
                "end_time": minutes_to_time(j_val + meetings["Jeffrey"]["duration"])
            }),
            (s_val, {
                "action": "meet", 
                "person": "Sarah", 
                "start_time": minutes_to_time(s_val), 
                "end_time": minutes_to_time(s_val + meetings["Sarah"]["duration"])
            }),
            (b_val, {
                "action": "meet", 
                "person": "Brian", 
                "start_time": minutes_to_time(b_val), 
                "end_time": minutes_to_time(b_val + meetings["Brian"]["duration"])
            })
        ]
        list_with_val.sort(key=lambda x: x[0])
        meetings_list = [item[1] for item in list_with_val]
        result = {"itinerary": meetings_list}
        print(f"SOLUTION: {result}")
    else:
        # Try scheduling pairs
        pairs = [
            (["Jeffrey", "Sarah"], "Brian"),
            (["Jeffrey", "Brian"], "Sarah"),
            (["Sarah", "Brian"], "Jeffrey")
        ]
        found = False
        result = None
        for pair, _ in pairs:
            schedule = schedule_pair(pair[0], pair[1])
            if schedule is not None:
                # Sort by start time
                schedule.sort(key=lambda x: x['start_time'])
                result = {"itinerary": schedule}
                found = True
                break
        
        if not found:
            # Schedule one meeting
            for meeting in ["Jeffrey", "Sarah", "Brian"]:
                schedule = schedule_one(meeting)
                if schedule is not None:
                    result = {"itinerary": schedule}
                    break
            if result is None:
                result = {"itinerary": []}
        
        print(f"SOLUTION: {result}")

if __name__ == "__main__":
    main()