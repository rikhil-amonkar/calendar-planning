from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Friends data
    friends = {
        "David": {"location": "Mission District", "available_start": 8*60, "available_end": 19*60+45, "min_duration": 45},
        "Kenneth": {"location": "Alamo Square", "available_start": 14*60, "available_end": 19*60+45, "min_duration": 120},
        "John": {"location": "Pacific Heights", "available_start": 17*60, "available_end": 20*60, "min_duration": 15},
        "Charles": {"location": "Union Square", "available_start": 21*60+45, "available_end": 22*60+45, "min_duration": 60},
        "Deborah": {"location": "Golden Gate Park", "available_start": 7*60, "available_end": 18*60+15, "min_duration": 90},
        "Karen": {"location": "Sunset District", "available_start": 17*60+45, "available_end": 21*60+15, "min_duration": 15},
        "Carol": {"location": "Presidio", "available_start": 8*60+15, "available_end": 9*60+15, "min_duration": 30}
    }

    # Travel times
    travel_times = {
        "Chinatown": {"Mission District": 18, "Alamo Square": 17, "Pacific Heights": 10, "Union Square": 7, 
                     "Golden Gate Park": 23, "Sunset District": 29, "Presidio": 19},
        "Mission District": {"Chinatown": 16, "Alamo Square": 11, "Pacific Heights": 16, "Union Square": 15,
                           "Golden Gate Park": 17, "Sunset District": 24, "Presidio": 25},
        "Alamo Square": {"Chinatown": 16, "Mission District": 10, "Pacific Heights": 10, "Union Square": 14,
                        "Golden Gate Park": 9, "Sunset District": 16, "Presidio": 18},
        "Pacific Heights": {"Chinatown": 11, "Mission District": 15, "Alamo Square": 10, "Union Square": 12,
                           "Golden Gate Park": 15, "Sunset District": 21, "Presidio": 11},
        "Union Square": {"Chinatown": 7, "Mission District": 14, "Alamo Square": 15, "Pacific Heights": 15,
                        "Golden Gate Park": 22, "Sunset District": 26, "Presidio": 24},
        "Golden Gate Park": {"Chinatown": 23, "Mission District": 17, "Alamo Square": 10, "Pacific Heights": 16,
                           "Union Square": 22, "Sunset District": 10, "Presidio": 11},
        "Sunset District": {"Chinatown": 30, "Mission District": 24, "Alamo Square": 17, "Pacific Heights": 21,
                          "Union Square": 30, "Golden Gate Park": 11, "Presidio": 16},
        "Presidio": {"Chinatown": 21, "Mission District": 26, "Alamo Square": 18, "Pacific Heights": 11,
                    "Union Square": 22, "Golden Gate Park": 12, "Sunset District": 15}
    }

    # Variables
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}
        s.add(start >= friends[name]["available_start"])
        s.add(end <= friends[name]["available_end"])
        s.add(end - start >= friends[name]["min_duration"])

    # Starting point
    current_time = 9 * 60  # 9:00 AM
    current_location = "Chinatown"

    # Try meeting Carol first since she's only available in the morning
    s.add(meeting_vars["Carol"]["start"] >= current_time)
    s.add(meeting_vars["Carol"]["end"] <= friends["Carol"]["available_end"])
    s.add(meeting_vars["Carol"]["end"] - meeting_vars["Carol"]["start"] >= friends["Carol"]["min_duration"])

    # After Carol, try meeting Deborah next (Golden Gate Park)
    s.add(meeting_vars["Deborah"]["start"] >= meeting_vars["Carol"]["end"] + 
         travel_times[friends["Carol"]["location"]][friends["Deborah"]["location"]])
    
    # Then try meeting David (Mission District)
    s.add(meeting_vars["David"]["start"] >= meeting_vars["Deborah"]["end"] + 
         travel_times[friends["Deborah"]["location"]][friends["David"]["location"]])
    
    # Then Kenneth (Alamo Square)
    s.add(meeting_vars["Kenneth"]["start"] >= meeting_vars["David"]["end"] + 
         travel_times[friends["David"]["location"]][friends["Kenneth"]["location"]])
    
    # Then John (Pacific Heights)
    s.add(meeting_vars["John"]["start"] >= meeting_vars["Kenneth"]["end"] + 
         travel_times[friends["Kenneth"]["location"]][friends["John"]["location"]])
    
    # Then Karen (Sunset District)
    s.add(meeting_vars["Karen"]["start"] >= meeting_vars["John"]["end"] + 
         travel_times[friends["John"]["location"]][friends["Karen"]["location"]])
    
    # Finally Charles (Union Square)
    s.add(meeting_vars["Charles"]["start"] >= meeting_vars["Karen"]["end"] + 
         travel_times[friends["Karen"]["location"]][friends["Charles"]["location"]])

    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        order = ["Carol", "Deborah", "David", "Kenneth", "John", "Karen", "Charles"]
        for name in order:
            start_val = model[meeting_vars[name]['start']].as_long()
            end_val = model[meeting_vars[name]['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_val//60:02d}:{start_val%60:02d}",
                "end_time": f"{end_val//60:02d}:{end_val%60:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))