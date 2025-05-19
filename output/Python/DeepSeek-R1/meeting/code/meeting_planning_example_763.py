import itertools
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        'Chinatown': {'Embarcadero':5,'Pacific Heights':10,'Russian Hill':7,'Haight-Ashbury':19,'Golden Gate Park':23,'Fisherman\'s Wharf':8,'Sunset District':29,'The Castro':22},
        'Embarcadero': {'Chinatown':7,'Pacific Heights':11,'Russian Hill':8,'Haight-Ashbury':21,'Golden Gate Park':25,'Fisherman\'s Wharf':6,'Sunset District':30,'The Castro':25},
        'Pacific Heights': {'Chinatown':11,'Embarcadero':10,'Russian Hill':7,'Haight-Ashbury':11,'Golden Gate Park':15,'Fisherman\'s Wharf':13,'Sunset District':21,'The Castro':16},
        'Russian Hill': {'Chinatown':9,'Embarcadero':8,'Pacific Heights':7,'Haight-Ashbury':17,'Golden Gate Park':21,'Fisherman\'s Wharf':7,'Sunset District':23,'The Castro':21},
        'Haight-Ashbury': {'Chinatown':19,'Embarcadero':20,'Pacific Heights':12,'Russian Hill':17,'Golden Gate Park':7,'Fisherman\'s Wharf':23,'Sunset District':15,'The Castro':6},
        'Golden Gate Park': {'Chinatown':23,'Embarcadero':25,'Pacific Heights':16,'Russian Hill':19,'Haight-Ashbury':7,'Fisherman\'s Wharf':24,'Sunset District':10,'The Castro':13},
        'Fisherman\'s Wharf': {'Chinatown':12,'Embarcadero':8,'Pacific Heights':12,'Russian Hill':7,'Haight-Ashbury':22,'Golden Gate Park':25,'Sunset District':27,'The Castro':27},
        'Sunset District': {'Chinatown':30,'Embarcadero':30,'Pacific Heights':21,'Russian Hill':24,'Haight-Ashbury':15,'Golden Gate Park':11,'Fisherman\'s Wharf':29,'The Castro':17},
        'The Castro': {'Chinatown':22,'Embarcadero':22,'Pacific Heights':16,'Russian Hill':18,'Haight-Ashbury':6,'Golden Gate Park':11,'Fisherman\'s Wharf':24,'Sunset District':17}
    }

    friends = [
        {'name':'Richard','location':'Embarcadero','start':915,'end':1125,'duration':90},
        {'name':'Mark','location':'Pacific Heights','start':900,'end':1020,'duration':45},
        {'name':'Matthew','location':'Russian Hill','start':1050,'end':1260,'duration':90},
        {'name':'Rebecca','location':'Haight-Ashbury','start':885,'end':1080,'duration':60},
        {'name':'Melissa','location':'Golden Gate Park','start':825,'end':1050,'duration':90},
        {'name':'Margaret','location':'Fisherman\'s Wharf','start':885,'end':1215,'duration':15},
        {'name':'Emily','location':'Sunset District','start':945,'end':1020,'duration':45},
        {'name':'George','location':'The Castro','start':840,'end':975,'duration':75}
    ]

    best_count = 0
    best_schedule = []
    best_end = float('inf')

    for perm in itertools.permutations(friends):
        current_time = 540
        current_loc = 'Chinatown'
        meetings = []
        valid = True

        for f in perm:
            try:
                travel = travel_times[current_loc][f['location']]
            except KeyError:
                valid = False
                break

            arrival = current_time + travel
            start = max(arrival, f['start'])
            end = start + f['duration']

            if end > f['end']:
                valid = False
                break

            meetings.append((f, start, end))
            current_time = end
            current_loc = f['location']

        if valid:
            cnt = len(meetings)
            if cnt > best_count or (cnt == best_count and current_time < best_end):
                best_count = cnt
                best_schedule = meetings
                best_end = current_time

    itinerary = []
    for meet in best_schedule:
        f = meet[0]
        start = minutes_to_time(meet[1])
        end = minutes_to_time(meet[2])
        itinerary.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": start,
            "end_time": end
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()