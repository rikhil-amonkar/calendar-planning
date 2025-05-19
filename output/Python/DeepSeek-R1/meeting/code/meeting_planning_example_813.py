import itertools
import json

def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}".replace(":00", "").replace(":0", ":")

travel_times = {
    'Marina District': {'Embarcadero':14,'Bayview':27,'Union Square':16,'Chinatown':15,'Sunset District':19,'Golden Gate Park':18,'Financial District':17,'Haight-Ashbury':16,'Mission District':20},
    'Embarcadero': {'Marina District':12,'Bayview':21,'Union Square':10,'Chinatown':7,'Sunset District':30,'Golden Gate Park':25,'Financial District':5,'Haight-Ashbury':21,'Mission District':20},
    'Bayview': {'Marina District':27,'Embarcadero':19,'Union Square':18,'Chinatown':19,'Sunset District':23,'Golden Gate Park':22,'Financial District':19,'Haight-Ashbury':19,'Mission District':13},
    'Union Square': {'Marina District':18,'Embarcadero':11,'Bayview':15,'Chinatown':7,'Sunset District':27,'Golden Gate Park':22,'Financial District':9,'Haight-Ashbury':18,'Mission District':14},
    'Chinatown': {'Marina District':12,'Embarcadero':5,'Bayview':20,'Union Square':7,'Sunset District':29,'Golden Gate Park':23,'Financial District':5,'Haight-Ashbury':19,'Mission District':17},
    'Sunset District': {'Marina District':21,'Embarcadero':30,'Bayview':22,'Union Square':30,'Chinatown':30,'Golden Gate Park':11,'Financial District':30,'Haight-Ashbury':15,'Mission District':25},
    'Golden Gate Park': {'Marina District':16,'Embarcadero':25,'Bayview':23,'Union Square':22,'Chinatown':23,'Sunset District':10,'Financial District':26,'Haight-Ashbury':7,'Mission District':17},
    'Financial District': {'Marina District':15,'Embarcadero':4,'Bayview':19,'Union Square':9,'Chinatown':5,'Sunset District':30,'Golden Gate Park':23,'Haight-Ashbury':19,'Mission District':17},
    'Haight-Ashbury': {'Marina District':17,'Embarcadero':20,'Bayview':18,'Union Square':19,'Chinatown':19,'Sunset District':15,'Golden Gate Park':7,'Financial District':21,'Mission District':11},
    'Mission District': {'Marina District':19,'Embarcadero':19,'Bayview':14,'Union Square':15,'Chinatown':16,'Sunset District':24,'Golden Gate Park':17,'Financial District':15,'Haight-Ashbury':12}
}

friends = [
    {'name':'Joshua','location':'Embarcadero','start':time_to_minutes('9:45'),'end':time_to_minutes('18:00'),'duration':105},
    {'name':'Jeffrey','location':'Bayview','start':time_to_minutes('9:45'),'end':time_to_minutes('20:15'),'duration':75},
    {'name':'Charles','location':'Union Square','start':time_to_minutes('10:45'),'end':time_to_minutes('20:15'),'duration':120},
    {'name':'Joseph','location':'Chinatown','start':time_to_minutes('7:00'),'end':time_to_minutes('15:30'),'duration':60},
    {'name':'Matthew','location':'Golden Gate Park','start':time_to_minutes('11:00'),'end':time_to_minutes('19:30'),'duration':45},
    {'name':'Carol','location':'Financial District','start':time_to_minutes('10:45'),'end':time_to_minutes('11:15'),'duration':15},
    {'name':'Paul','location':'Haight-Ashbury','start':time_to_minutes('19:15'),'end':time_to_minutes('20:30'),'duration':15},
    {'name':'Rebecca','location':'Mission District','start':time_to_minutes('17:00'),'end':time_to_minutes('21:45'),'duration':45}
]

best = []
max_count = 0

for perm in itertools.permutations(friends):
    current_loc = 'Marina District'
    current_time = 540
    schedule = []
    valid = True
    
    for f in perm:
        if current_loc not in travel_times or f['location'] not in travel_times[current_loc]:
            valid = False
            break
        travel = travel_times[current_loc][f['location']]
        arrive = current_time + travel
        start = max(arrive, f['start'])
        end = start + f['duration']
        if end > f['end']:
            valid = False
            break
        schedule.append({'friend':f, 'start':start, 'end':end})
        current_time = end
        current_loc = f['location']
    
    if valid and len(schedule) > max_count:
        max_count = len(schedule)
        best = schedule
    elif valid and len(schedule) == max_count and current_time < (best[-1]['end'] if best else float('inf')):
        best = schedule

itinerary = []
for item in best:
    f = item['friend']
    itinerary.append({
        "action": "meet",
        "location": f['location'],
        "person": f['name'],
        "start_time": minutes_to_time(item['start']),
        "end_time": minutes_to_time(item['end'])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))