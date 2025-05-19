import itertools
import json

def main():
    travel_time = {
        'Sunset District': {'Alamo Square':17, 'Russian Hill':24, 'Golden Gate Park':11, 'Mission District':24},
        'Alamo Square': {'Sunset District':16, 'Russian Hill':13, 'Golden Gate Park':9, 'Mission District':10},
        'Russian Hill': {'Sunset District':23, 'Alamo Square':15, 'Golden Gate Park':21, 'Mission District':16},
        'Golden Gate Park': {'Sunset District':10, 'Alamo Square':10, 'Russian Hill':19, 'Mission District':17},
        'Mission District': {'Sunset District':24, 'Alamo Square':11, 'Russian Hill':15, 'Golden Gate Park':17}
    }

    friends = [
        {'name':'Charles', 'location':'Alamo Square', 'start_time':18*60, 'end_time':20*60+45, 'duration':90},
        {'name':'Margaret', 'location':'Russian Hill', 'start_time':9*60, 'end_time':16*60, 'duration':30},
        {'name':'Daniel', 'location':'Golden Gate Park', 'start_time':8*60, 'end_time':13*60+30, 'duration':15},
        {'name':'Stephanie', 'location':'Mission District', 'start_time':20*60+30, 'end_time':22*60, 'duration':90}
    ]

    best_count = 0
    best_itinerary = []
    current_location = 'Sunset District'
    start_time = 9 * 60  # 9:00 AM

    for perm in itertools.permutations(friends):
        itinerary = []
        ct = start_time
        cl = current_location
        valid = True
        temp_count = 0

        for f in perm:
            try:
                tt = travel_time[cl][f['location']]
            except KeyError:
                valid = False
                break
            arrival = ct + tt
            earliest_start = max(arrival, f['start_time'])
            latest_start = f['end_time'] - f['duration']
            if earliest_start > latest_start:
                valid = False
                break
            meeting_end = earliest_start + f['duration']
            itinerary.append({
                'friend': f,
                'start': earliest_start,
                'end': meeting_end,
                'location': f['location']
            })
            ct = meeting_end
            cl = f['location']
            temp_count += 1

        if valid and temp_count > best_count:
            best_count = temp_count
            best_itinerary = itinerary
        elif valid and temp_count == best_count and best_itinerary:
            if ct < best_itinerary[-1]['end']:
                best_itinerary = itinerary

    formatted = []
    for event in best_itinerary:
        sh = event['start'] // 60
        sm = event['start'] % 60
        eh = event['end'] // 60
        em = event['end'] % 60
        start_str = f"{sh}:{sm:02d}".replace(":00", ":0").replace(":0", ":") if sm ==0 else f"{sh}:{sm:02d}"
        end_str = f"{eh}:{em:02d}".replace(":00", ":0").replace(":0", ":") if em ==0 else f"{eh}:{em:02d}"
        formatted.append({
            "action": "meet",
            "location": event['friend']['location'],
            "person": event['friend']['name'],
            "start_time": f"{sh}:{sm:02d}".replace(':00', ':0'),
            "end_time": f"{eh}:{em:02d}".replace(':00', ':0')
        })

    print(json.dumps({"itinerary": formatted}, indent=2))

if __name__ == "__main__":
    main()