import itertools
import json

def main():
    travel_times = {
        "Embarcadero": {"Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20, "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12},
        "Bayview": {"Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32, "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27},
        "Chinatown": {"Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19, "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12},
        "Alamo Square": {"Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17, "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15},
        "Nob Hill": {"Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17, "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11},
        "Presidio": {"Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18, "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11},
        "Union Square": {"Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9, "Presidio": 24, "The Castro": 17, "North Beach": 10, "Fisherman's Wharf": 15, "Marina District": 18},
        "The Castro": {"Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16, "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 24, "Marina District": 21},
        "North Beach": {"Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7, "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9},
        "Fisherman's Wharf": {"Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 9},
        "Marina District": {"Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12, "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10}
    }
    
    meetings = [
        {"person": "Matthew", "location": "Bayview", "start_avail": 615, "end_avail": 780, "min_duration": 120},
        {"person": "Karen", "location": "Chinatown", "start_avail": 615, "end_avail": 735, "min_duration": 90},
        {"person": "Sarah", "location": "Alamo Square", "start_avail": 660, "end_avail": 765, "min_duration": 105},
        {"person": "Jessica", "location": "Nob Hill", "start_avail": 450, "end_avail": 585, "min_duration": 120},
        {"person": "Mary", "location": "Union Square", "start_avail": 465, "end_avail": 750, "min_duration": 60},
        {"person": "Charles", "location": "The Castro", "start_avail": 450, "end_avail": 780, "min_duration": 105},
        {"person": "Nancy", "location": "North Beach", "start_avail": 345, "end_avail": 660, "min_duration": 15},
        {"person": "Thomas", "location": "Fisherman's Wharf", "start_avail": 270, "end_avail": 600, "min_duration": 30},
        {"person": "Brian", "location": "Marina District", "start_avail": 195, "end_avail": 540, "min_duration": 60}
    ]
    
    best_count = 0
    best_total_time = 0
    best_itinerary = []
    
    for perm in itertools.permutations(meetings):
        current_time = 0
        current_location = "Embarcadero"
        itinerary = []
        count = 0
        total_time = 0
        
        for meeting in perm:
            travel_time = travel_times[current_location][meeting["location"]]
            arrival_time = current_time + travel_time
            start_meeting = max(arrival_time, meeting["start_avail"])
            end_meeting = start_meeting + meeting["min_duration"]
            
            if end_meeting <= meeting["end_avail"]:
                itinerary.append({
                    "action": "meet",
                    "location": meeting["location"],
                    "person": meeting["person"],
                    "start_time": minutes_to_time(start_meeting),
                    "end_time": minutes_to_time(end_meeting)
                })
                count += 1
                total_time += meeting["min_duration"]
                current_time = end_meeting
                current_location = meeting["location"]
        
        if count > best_count or (count == best_count and total_time > best_total_time):
            best_count = count
            best_total_time = total_time
            best_itinerary = itinerary
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()