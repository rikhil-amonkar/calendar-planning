from z3 import *
import json

def main():
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Bayview'): 19,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Bayview'): 22,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Alamo Square'): 16,
    }
    
    meetings = [
        {'name': 'Nancy', 'location': 'Chinatown', 'start_min': 30, 'end_min': 270, 'duration': 90},
        {'name': 'Mary', 'location': 'Alamo Square', 'start_min': -120, 'end_min': 720, 'duration': 75},
        {'name': 'Jessica', 'location': 'Bayview', 'start_min': 135, 'end_min': 285, 'duration': 45}
    ]
    
    met_vars = [Bool(meeting['name']) for meeting in meetings]
    start_vars = [Int(meeting['name'] + '_start') for meeting in meetings]
    
    pairs = []
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            pairs.append((i, j, Bool(f"{meetings[i]['name']}_before_{meetings[j]['name']}")))
    
    s = Optimize()
    
    for i, meeting in enumerate(meetings):
        s.add(Implies(met_vars[i], And(
            start_vars[i] >= meeting['start_min'],
            start_vars[i] <= meeting['end_min'] - meeting['duration'],
            start_vars[i] >= travel_times[('Financial District', meeting['location'])]
        )))
    
    for (i, j, order_var) in pairs:
        meeting_i = meetings[i]
        meeting_j = meetings[j]
        travel_ij = travel_times[(meeting_i['location'], meeting_j['location'])]
        travel_ji = travel_times[(meeting_j['location'], meeting_i['location'])]
        
        s.add(Implies(And(met_vars[i], met_vars[j]), 
            Or(
                And(order_var, start_vars[i] + meeting_i['duration'] + travel_ij <= start_vars[j]),
                And(Not(order_var), start_vars[j] + meeting_j['duration'] + travel_ji <= start_vars[i])
            )))
    
    s.maximize(Sum([If(m, 1, 0) for m in met_vars]))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i, meeting in enumerate(meetings):
            if is_true(model[met_vars[i]]):
                start_val = model.evaluate(start_vars[i]).as_long()
                total_minutes = start_val
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                start_time_str = f"{hours}:{minutes:02d}"
                
                end_minutes = start_val + meeting['duration']
                hours_end = 9 + end_minutes // 60
                minutes_end = end_minutes % 60
                end_time_str = f"{hours_end}:{minutes_end:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "location": meeting['location'],
                    "person": meeting['name'],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        
        itinerary.sort(key=lambda x: x['start_time'])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()