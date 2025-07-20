import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Embarcadero": {
            "Richmond District": 21,
            "Union Square": 10,
            "Financial District": 5,
            "Pacific Heights": 11,
            "Nob Hill": 10,
            "Bayview": 21
        },
        "Richmond District": {
            "Embarcadero": 19,
            "Union Square": 21,
            "Financial District": 22,
            "Pacific Heights": 10,
            "Nob Hill": 17,
            "Bayview": 26
        },
        "Union Square": {
            "Embarcadero": 11,
            "Richmond District": 20,
            "Financial District": 9,
            "Pacific Heights": 15,
            "Nob Hill": 9,
            "Bayview": 15
        },
        "Financial District": {
            "Embarcadero": 4,
            "Richmond District": 21,
            "Union Square": 9,
            "Pacific Heights": 13,
            "Nob Hill": 8,
            "Bayview": 19
        },
        "Pacific Heights": {
            "Embarcadero": 10,
            "Richmond District": 12,
            "Union Square": 12,
            "Financial District": 13,
            "Nob Hill": 8,
            "Bayview": 22
        },
        "Nob Hill": {
            "Embarcadero": 9,
            "Richmond District": 14,
            "Union Square": 7,
            "Financial District": 9,
            "Pacific Heights": 8,
            "Bayview": 19
        },
        "Bayview": {
            "Embarcadero": 19,
            "Richmond District": 25,
            "Union Square": 17,
            "Financial District": 19,
            "Pacific Heights": 23,
            "Nob Hill": 20
        }
    }
    
    friends = [
        {"name": "Kenneth", "location": "Richmond District", "start_minutes": 21*60+15, "end_minutes": 22*60, "min_duration": 30},
        {"name": "Lisa", "location": "Union Square", "start_minutes": 9*60, "end_minutes": 16*60+30, "min_duration": 45},
        {"name": "Joshua", "location": "Financial District", "start_minutes": 12*60, "end_minutes": 15*60+15, "min_duration": 15},
        {"name": "Nancy", "location": "Pacific Heights", "start_minutes": 8*60, "end_minutes": 11*60+30, "min_duration": 90},
        {"name": "Andrew", "location": "Nob Hill", "start_minutes": 11*60+30, "end_minutes": 20*60+15, "min_duration": 60},
        {"name": "John", "location": "Bayview", "start_minutes": 16*60+45, "end_minutes": 21*60+30, "min_duration": 75}
    ]
    
    best_itinerary = None
    max_met = 0
    found = False
    for r in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(subset):
                current_location = "Embarcadero"
                current_time = 540
                itinerary = []
                feasible = True
                for friend in perm:
                    if current_location not in travel_times or friend["location"] not in travel_times[current_location]:
                        feasible = False
                        break
                    travel_time = travel_times[current_location][friend["location"]]
                    arrival_time = current_time + travel_time
                    start_time = max(arrival_time, friend["start_minutes"])
                    if start_time + friend["min_duration"] > friend["end_minutes"]:
                        feasible = False
                        break
                    end_time = start_time + friend["min_duration"]
                    itinerary.append({
                        "friend": friend,
                        "start_minutes": start_time,
                        "end_minutes": end_time
                    })
                    current_time = end_time
                    current_location = friend["location"]
                if feasible:
                    best_itinerary = itinerary
                    max_met = r
                    found = True
                    break
            if found:
                break
        if found:
            break
            
    result = {"itinerary": []}
    if best_itinerary:
        for item in best_itinerary:
            friend = item["friend"]
            result["itinerary"].append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(item["start_minutes"]),
                "end_time": minutes_to_time(item["end_minutes"])
            })
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()