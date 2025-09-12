from z3 import *
import json

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        'Presidio': {
            'Marina District': 11,
            'The Castro': 21,
            'Fisherman\'s Wharf': 19,
            'Bayview': 31,
            'Pacific Heights': 11,
            'Mission District': 26,
            'Alamo Square': 19,
            'Golden Gate Park': 12
        },
        'Marina District': {
            'Presidio': 10,
            'The Castro': 22,
            'Fisherman\'s Wharf': 10,
            'Bayview': 27,
            'Pacific Heights': 7,
            'Mission District': 20,
            'Alamo Square': 15,
            'Golden Gate Park': 18
        },
        'The Castro': {
            'Presidio': 20,
            'Marina District': 21,
            'Fisherman\'s Wharf': 24,
            'Bayview': 19,
            'Pacific Heights': 16,
            'Mission District': 7,
            'Alamo Square': 8,
            'Golden Gate Park': 11
        },
        'Fisherman\'s Wharf': {
            'Presidio': 17,
            'Marina District': 9,
            'The Castro': 27,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Mission District': 22,
            'Alamo Square': 21,
            'Golden Gate Park': 25
        },
        'Bayview': {
            'Presidio': 32,
            'Marina District': 27,
            'The Castro': 19,
            'Fisherman\'s Wharf': 25,
            'Pacific Heights': 23,
            'Mission District': 13,
            'Alamo Square': 16,
            'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'Presidio': 11,
            'Marina District': 6,
            'The Castro': 16,
            'Fisherman\'s Wharf': 13,
            'Bayview': 22,
            'Mission District': 15,
            'Alamo Square': 10,
            'Golden Gate Park': 15
        },
        'Mission District': {
            'Presidio': 25,
            'Marina District': 19,
            'The Castro': 7,
            'Fisherman\'s Wharf': 22,
            'Bayview': 14,
            'Pacific Heights': 16,
            'Alamo Square': 11,
            'Golden Gate Park': 17
        },
        'Alamo Square': {
            'Presidio': 17,
            'Marina District': 15,
            'The Castro': 8,
            'Fisherman\'s Wharf': 19,
            'Bayview': 16,
            'Pacific Heights': 10,
            'Mission District': 10,
            'Golden Gate Park': 9
        },
        'Golden Gate Park': {
            'Presidio': 11,
            'Marina District': 16,
            'The Castro': 13,
            'Fisherman\'s Wharf': 24,
            'Bayview': 23,
            'Pacific Heights': 16,
            'Mission District': 17,
            'Alamo Square': 9
        }
    }
    
    friends = [
        {'name': 'Amanda', 'loc': 'Marina District', 'start_avail': 14*60+45, 'end_avail': 19*60+30, 'min_dur': 105},
        {'name': 'Melissa', 'loc': 'The Castro', 'start_avail': 9*60+30, 'end_avail': 17*60, 'min_dur': 30},
        {'name': 'Jeffrey', 'loc': 'Fisherman\'s Wharf', 'start_avail': 12*60+45, 'end_avail': 18*60+45, 'min_dur': 120},
        {'name': 'Matthew', 'loc': 'Bayview', 'start_avail': 10*60+15, 'end_avail': 13*60+15, 'min_dur': 30},
        {'name': 'Nancy', 'loc': 'Pacific Heights', 'start_avail': 17*60, 'end_avail': 21*60+30, 'min_dur': 105},
        {'name': 'Karen', 'loc': 'Mission District', 'start_avail': 17*60+30, 'end_avail': 20*60+30, 'min_dur': 105},
        {'name': 'Robert', 'loc': 'Alamo Square', 'start_avail': 11*60+15, 'end_avail': 17*60+30, 'min_dur': 120},
        {'name': 'Joseph', 'loc': 'Golden Gate Park', 'start_avail': 8*60+30, 'end_avail': 21*60+15, 'min_dur': 105}
    ]
    
    n = len(friends)
    opt = Optimize()
    
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    locs = ['Presidio'] + [f['loc'] for f in friends]
    
    for i in range(n):
        opt.add(If(met[i],
                   And(start[i] >= friends[i]['start_avail'],
                       end[i] <= friends[i]['end_avail'],
                       end[i] - start[i] >= friends[i]['min_dur']),
                   True))
    
    dummy_start = 540
    dummy_end = 540
    dummy_loc = 'Presidio'
    
    for i in range(-1, n):
        for j in range(-1, n):
            if i == j:
                continue
            if i == -1 and j == -1:
                continue
            condition = True
            if i == -1:
                condition = And(condition, met[j])
                loc_i = dummy_loc
                start_i = dummy_start
                end_i = dummy_end
            else:
                condition = And(condition, met[i])
                loc_i = locs[i+1]
                start_i = start[i]
                end_i = end[i]
            if j == -1:
                condition = And(condition, met[i])
                loc_j = dummy_loc
                start_j = dummy_start
                end_j = dummy_end
            else:
                condition = And(condition, met[j])
                loc_j = locs[j+1]
                start_j = start[j]
                end_j = end[j]
            
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]
            
            opt.add(If(condition,
                       Or(start_j >= end_i + travel_ij,
                          start_i >= end_j + travel_ji),
                       True))
    
    opt.maximize(Sum([If(m, 1, 0) for m in met]))
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if is_true(model.eval(met[i])):
                s = model.eval(start[i]).as_long()
                e = model.eval(end[i]).as_long()
                scheduled_meetings.append({
                    'action': 'meet',
                    'location': friends[i]['loc'],
                    'person': friends[i]['name'],
                    'start_time': convert_minutes_to_time(s),
                    'end_time': convert_minutes_to_time(e)
                })
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {'itinerary': scheduled_meetings}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()