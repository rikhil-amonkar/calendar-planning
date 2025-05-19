import json

def time_to_min(t_str):
    hours, mins = map(int, t_str.split(':'))
    return hours * 60 + mins

def min_to_time(m):
    hours, mins = divmod(m, 60)
    return f"{hours}:{mins:02d}"

travel_times = {
    'Embarcadero': {'Richmond District':21,'Union Square':10,'Financial District':5,'Pacific Heights':11,'Nob Hill':10,'Bayview':21},
    'Richmond District':{'Embarcadero':19,'Union Square':21,'Financial District':22,'Pacific Heights':10,'Nob Hill':17,'Bayview':26},
    'Union Square':{'Embarcadero':11,'Richmond District':20,'Financial District':9,'Pacific Heights':15,'Nob Hill':9,'Bayview':15},
    'Financial District':{'Embarcadero':4,'Richmond District':21,'Union Square':9,'Pacific Heights':13,'Nob Hill':8,'Bayview':19},
    'Pacific Heights':{'Embarcadero':10,'Richmond District':12,'Union Square':12,'Financial District':13,'Nob Hill':8,'Bayview':22},
    'Nob Hill':{'Embarcadero':9,'Richmond District':14,'Union Square':7,'Financial District':9,'Pacific Heights':8,'Bayview':19},
    'Bayview':{'Embarcadero':19,'Richmond District':25,'Union Square':17,'Financial District':19,'Pacific Heights':23,'Nob Hill':20}
}

friends = [
    {'name':'Nancy','location':'Pacific Heights','start':'8:00','end':'11:30','duration':90},
    {'name':'Lisa','location':'Union Square','start':'9:00','end':'16:30','duration':45},
    {'name':'Andrew','location':'Nob Hill','start':'11:30','end':'20:15','duration':60},
    {'name':'Joshua','location':'Financial District','start':'12:00','end':'15:15','duration':15},
    {'name':'John','location':'Bayview','start':'16:45','end':'21:30','duration':75},
    {'name':'Kenneth','location':'Richmond District','start':'21:15','end':'22:00','duration':30}
]

itinerary = []
current_loc = 'Embarcadero'
current_time = time_to_min('9:00')

for f in friends:
    loc = f['location']
    start = time_to_min(f['start'])
    end = time_to_min(f['end'])
    dur = f['duration']
    travel = travel_times[current_loc][loc]
    arrive = current_time + travel
    start_time = max(arrive, start)
    if start_time + dur > end:
        continue
    itinerary.append({
        'action':'meet',
        'location':loc,
        'person':f['name'],
        'start_time':min_to_time(start_time).replace(':0', ':') if min_to_time(start_time).endswith(':00') else min_to_time(start_time).lstrip('0'),
        'end_time':min_to_time(start_time + dur).replace(':0', ':') if min_to_time(start_time + dur).endswith(':00') else min_to_time(start_time + dur).lstrip('0')
    })
    current_time = start_time + dur
    current_loc = loc

print(json.dumps({'itinerary':itinerary}, indent=2))