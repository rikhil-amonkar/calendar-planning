import itertools
import json

def time_to_min(timestr):
    h, m = map(int, timestr.split(':'))
    return h * 60 + m

def min_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

friends = [
    {'name':'Rebecca','location':'Bayview','start':time_to_min('9:00'),'end':time_to_min('12:45'),'duration':90},
    {'name':'Amanda','location':'Pacific Heights','start':time_to_min('18:30'),'end':time_to_min('21:45'),'duration':90},
    {'name':'James','location':'Alamo Square','start':time_to_min('9:45'),'end':time_to_min('21:15'),'duration':90},
    {'name':'Sarah','location':'Fisherman\'s Wharf','start':time_to_min('8:00'),'end':time_to_min('21:30'),'duration':90},
    {'name':'Melissa','location':'Golden Gate Park','start':time_to_min('9:00'),'end':time_to_min('18:45'),'duration':90}
]

travel_times = {
    'The Castro': {'Bayview':19,'Pacific Heights':16,'Alamo Square':8,'Fisherman\'s Wharf':24,'Golden Gate Park':11},
    'Bayview': {'The Castro':20,'Pacific Heights':23,'Alamo Square':16,'Fisherman\'s Wharf':25,'Golden Gate Park':22},
    'Pacific Heights': {'The Castro':16,'Bayview':22,'Alamo Square':10,'Fisherman\'s Wharf':13,'Golden Gate Park':15},
    'Alamo Square': {'The Castro':8,'Bayview':16,'Pacific Heights':10,'Fisherman\'s Wharf':19,'Golden Gate Park':9},
    'Fisherman\'s Wharf': {'The Castro':26,'Bayview':26,'Pacific Heights':12,'Alamo Square':20,'Golden Gate Park':25},
    'Golden Gate Park': {'The Castro':13,'Bayview':23,'Pacific Heights':16,'Alamo Square':10,'Fisherman\'s Wharf':24}
}

best_count = 0
best_itinerary = []
best_end = float('inf')

for perm in itertools.permutations(friends):
    current_time = 540
    current_loc = 'The Castro'
    schedule = []
    met = set()
    for f in perm:
        if f['name'] in met:
            continue
        loc = f['location']
        tt = travel_times[current_loc].get(loc,0)
        arrive = current_time + tt
        earliest_start = max(arrive, f['start'])
        latest_start = f['end'] - f['duration']
        if earliest_start > latest_start:
            continue
        start = earliest_start
        end = start + f['duration']
        schedule.append({'name':f['name'],'loc':loc,'start':start,'end':end})
        met.add(f['name'])
        current_time = end
        current_loc = loc
    if len(met) > best_count or (len(met) == best_count and current_time < best_end):
        best_count = len(met)
        best_end = current_time
        best_itinerary = sorted(schedule, key=lambda x: x['start'])

output = {"itinerary": []}
for item in best_itinerary:
    output["itinerary"].append({
        "action": "meet",
        "location": item['loc'],
        "person": item['name'],
        "start_time": min_to_time(item['start']),
        "end_time": min_to_time(item['end'])
    })

print(json.dumps(output, indent=2))