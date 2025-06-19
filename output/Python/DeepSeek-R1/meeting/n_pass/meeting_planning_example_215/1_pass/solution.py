import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Bayview": {
            "Embarcadero": 19,
            "Richmond District": 25,
            "Fisherman's Wharf": 25
        },
        "Embarcadero": {
            "Bayview": 21,
            "Richmond District": 21,
            "Fisherman's Wharf": 6
        },
        "Richmond District": {
            "Bayview": 26,
            "Embarcadero": 19,
            "Fisherman's Wharf": 18
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Embarcadero": 8,
            "Richmond District": 18
        }
    }
    
    meetings_list = [
        {"name": "Jessica", "location": "Embarcadero", "start_avail": 16*60+45, "end_avail": 19*60, "min_duration": 30},
        {"name": "Sandra", "location": "Richmond District", "start_avail": 18*60+30, "end_avail": 21*60+45, "min_duration": 120},
        {"name": "Jason", "location": "Fisherman's Wharf", "start_avail": 16*60, "end_avail": 16*60+45, "min_duration": 30}
    ]
    
    masks = list(itertools.product([0,1], repeat=3))
    masks = [m for m in masks if sum(m) > 0]
    masks_sorted = sorted(masks, key=lambda x: sum(x), reverse=True)
    
    best_count = 0
    best_itinerary = None
    
    for perm in itertools.permutations(meetings_list):
        for mask in masks_sorted:
            current_time = 540
            current_location = 'Bayview'
            itinerary = []
            valid = True
            for i in range(3):
                if mask[i] == 1:
                    meeting = perm[i]
                    travel_duration = travel_times[current_location][meeting['location']]
                    arrival = current_time + travel_duration
                    start_meeting = max(meeting['start_avail'], arrival)
                    if start_meeting + meeting['min_duration'] <= meeting['end_avail']:
                        end_meeting = start_meeting + meeting['min_duration']
                        itinerary.append({
                            'meeting': meeting,
                            'start': start_meeting,
                            'end': end_meeting
                        })
                        current_time = end_meeting
                        current_location = meeting['location']
                    else:
                        valid = False
                        break
            if valid:
                count = len(itinerary)
                if count > best_count:
                    best_count = count
                    best_itinerary = itinerary
                    if best_count == 3:
                        break
            if best_count == 3:
                break
        if best_count == 3:
            break
    
    if best_itinerary is None:
        output_itinerary = []
    else:
        output_itinerary = []
        for item in best_itinerary:
            meeting = item['meeting']
            output_itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['name'],
                "start_time": format_time(item['start']),
                "end_time": format_time(item['end'])
            })
    
    result = {
        "itinerary": output_itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()