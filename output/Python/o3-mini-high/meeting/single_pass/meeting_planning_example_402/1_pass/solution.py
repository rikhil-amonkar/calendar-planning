#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Union Square'): 17,
        
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Union Square'): 30,
        
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Union Square'): 16,
        
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Sunset District'): 31,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Union Square'): 9,
        
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Financial District'): 9
    }
    
    # Meeting constraints:
    # Times are in minutes from midnight.
    # 9:00 AM = 540, 9:15 AM = 555, 10:15 AM = 615, 12:00 PM = 720, etc.
    meetings = {
        "Sarah": {
            "location": "Haight-Ashbury",
            "availability_start": 17 * 60,         # 17:00 -> 1020 minutes
            "availability_end": 21 * 60 + 30,       # 21:30 -> 1290 minutes
            "min_duration": 105
        },
        "Patricia": {
            "location": "Sunset District",
            "availability_start": 17 * 60,         # 17:00 -> 1020 minutes
            "availability_end": 19 * 60 + 45,       # 19:45 -> 1185 minutes
            "min_duration": 45
        },
        "Matthew": {
            "location": "Marina District",
            "availability_start": 9 * 60 + 15,       # 9:15 -> 555 minutes
            "availability_end": 12 * 60,             # 12:00 -> 720 minutes
            "min_duration": 15
        },
        "Joseph": {
            "location": "Financial District",
            "availability_start": 14 * 60 + 15,      # 14:15 -> 855 minutes
            "availability_end": 18 * 60 + 45,        # 18:45 -> 1125 minutes
            "min_duration": 30
        },
        "Robert": {
            "location": "Union Square",
            "availability_start": 10 * 60 + 15,      # 10:15 -> 615 minutes
            "availability_end": 21 * 60 + 45,        # 21:45 -> 1305 minutes
            "min_duration": 15
        }
    }
    
    itinerary = []
    # Start at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 540 minutes
    current_location = "Golden Gate Park"
    
    # 1. Meet Matthew at Marina District
    travel = travel_times[(current_location, meetings["Matthew"]["location"])]
    current_time += travel  # travel from Golden Gate Park to Marina District
    meeting_start = max(current_time, meetings["Matthew"]["availability_start"])
    meeting_end = meeting_start + meetings["Matthew"]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Matthew"]["location"],
        "person": "Matthew",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Matthew"]["location"]
    
    # 2. Meet Robert at Union Square
    travel = travel_times[(current_location, meetings["Robert"]["location"])]
    current_time += travel  # travel from Marina District to Union Square
    meeting_start = max(current_time, meetings["Robert"]["availability_start"])
    meeting_end = meeting_start + meetings["Robert"]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Robert"]["location"],
        "person": "Robert",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Robert"]["location"]
    
    # 3. Meet Joseph at Financial District
    travel = travel_times[(current_location, meetings["Joseph"]["location"])]
    current_time += travel  # travel from Union Square to Financial District
    meeting_start = max(current_time, meetings["Joseph"]["availability_start"])
    meeting_end = meeting_start + meetings["Joseph"]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Joseph"]["location"],
        "person": "Joseph",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Joseph"]["location"]
    
    # 4. Meet Sarah at Haight-Ashbury
    travel = travel_times[(current_location, meetings["Sarah"]["location"])]
    current_time += travel  # travel from Financial District to Haight-Ashbury
    meeting_start = max(current_time, meetings["Sarah"]["availability_start"])
    meeting_end = meeting_start + meetings["Sarah"]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Sarah"]["location"],
        "person": "Sarah",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Sarah"]["location"]
    
    # 5. Meet Patricia at Sunset District
    travel = travel_times[(current_location, meetings["Patricia"]["location"])]
    current_time += travel  # travel from Haight-Ashbury to Sunset District
    meeting_start = max(current_time, meetings["Patricia"]["availability_start"])
    meeting_end = meeting_start + meetings["Patricia"]["min_duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Patricia"]["location"],
        "person": "Patricia",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Patricia"]["location"]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()