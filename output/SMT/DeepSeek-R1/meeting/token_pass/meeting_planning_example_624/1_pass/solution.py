from z3 import *
import json

def main():
    # Travel times dictionary: (from, to) -> minutes
    travel_dict = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Russian Hill'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Russian Hill'): 4,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5
    }
    
    friends_data = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'avail_start': 750, 'avail_end': 810, 'min_duration': 60},
        {'name': 'Laura', 'location': 'Fisherman\'s Wharf', 'avail_start': 165, 'avail_end': 750, 'min_duration': 60},
        {'name': 'Karen', 'location': 'The Castro', 'avail_start': 0, 'avail_end': 300, 'min_duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'avail_start': 195, 'avail_end': 750, 'min_duration': 75},
        {'name': 'Deborah', 'location': 'Alamo Square', 'avail_start': 180, 'avail_end': 360, 'min_duration': 105},
        {'name': 'Jason', 'location': 'North Beach', 'avail_start': 345, 'avail_end': 600, 'min_duration': 90},
        {'name': 'Steven', 'location': 'Russian Hill', 'avail_start': 345, 'avail_end': 570, 'min_duration': 120}
    ]
    
    s = Solver()
    
    included_vars = [Bool(f'included_{i}') for i in range(len(friends_data))]
    start_vars = [Real(f'start_{i}') for i in range(len(friends_data))]
    end_vars = [Real(f'end_{i}') for i in range(len(friends_data))]
    
    for i, friend in enumerate(friends_data):
        s.add(Implies(included_vars[i], start_vars[i] >= friend['avail_start']))
        s.add(Implies(included_vars[i], end_vars[i] <= friend['avail_end']))
        s.add(Implies(included_vars[i], end_vars[i] - start_vars[i] >= friend['min_duration']))
        s.add(Implies(included_vars[i], start_vars[i] >= 0))
        
        travel_time = travel_dict[('Golden Gate Park', friend['location'])]
        s.add(Implies(included_vars[i], start_vars[i] >= travel_time))
    
    for i in range(len(friends_data)):
        for j in range(i+1, len(friends_data)):
            loc_i = friends_data[i]['location']
            loc_j = friends_data[j]['location']
            travel_ij = travel_dict[(loc_i, loc_j)]
            travel_ji = travel_dict[(loc_j, loc_i)]
            s.add(Implies(And(included_vars[i], included_vars[j]),
                           Or(end_vars[i] + travel_ij <= start_vars[j],
                              end_vars[j] + travel_ji <= start_vars[i])))
    
    objective = Sum([If(included_vars[i], 1, 0) for i in range(len(friends_data))])
    s.maximize(objective)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i, friend in enumerate(friends_data):
            if is_true(m.evaluate(included_vars[i])):
                start_val = m.evaluate(start_vars[i])
                end_val = m.evaluate(end_vars[i])
                start_minutes = float(start_val.as_fraction())
                end_minutes = float(end_val.as_fraction())
                start_time = convert_to_time(start_minutes)
                end_time = convert_to_time(end_minutes)
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

def convert_to_time(minutes):
    total_minutes = 9 * 60 + minutes
    hours = int(total_minutes // 60)
    mins = int(total_minutes % 60)
    return f"{hours}:{mins:02d}"

if __name__ == '__main__':
    main()