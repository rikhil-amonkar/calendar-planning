import z3
import json

def main():
    # Define travel times dictionary
    travel_times = {
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Bayview'): 27,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Bayview'): 20,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Bayview'): 22,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Bayview'): 16,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Bayview'): 19,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Bayview'): 25,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Bayview'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Bayview'): 31,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Golden Gate Park'): 22
    }
    
    def get_travel_time(from_loc, to_loc):
        if from_loc == to_loc:
            return 0
        return travel_times[(from_loc, to_loc)]
    
    # Define meetings with converted times (minutes from 9:00 AM)
    meetings = [
        {'name': 'Robert', 'location': 'Chinatown', 'avail_start': -75, 'avail_end': 510, 'min_dur': 120},
        {'name': 'David', 'location': 'Sunset District', 'avail_start': 210, 'avail_end': 645, 'min_dur': 45},
        {'name': 'Matthew', 'location': 'Alamo Square', 'avail_start': -15, 'avail_end': 285, 'min_dur': 90},
        {'name': 'Jessica', 'location': 'Financial District', 'avail_start': 30, 'avail_end': 585, 'min_dur': 45},
        {'name': 'Melissa', 'location': 'North Beach', 'avail_start': -105, 'avail_end': 465, 'min_dur': 45},
        {'name': 'Mark', 'location': 'Embarcadero', 'avail_start': 375, 'avail_end': 480, 'min_dur': 45},
        {'name': 'Deborah', 'location': 'Presidio', 'avail_start': 600, 'avail_end': 645, 'min_dur': 45},
        {'name': 'Karen', 'location': 'Golden Gate Park', 'avail_start': 630, 'avail_end': 780, 'min_dur': 120},
        {'name': 'Laura', 'location': 'Bayview', 'avail_start': 735, 'avail_end': 795, 'min_dur': 15}
    ]
    
    n = len(meetings)
    solver = z3.Solver()
    opt = z3.Optimize()
    
    # Create Z3 variables for each meeting
    s = [z3.Int(f's_{i}') for i in range(n)]
    e = [z3.Int(f'e_{i}') for i in range(n)]
    scheduled = [z3.Bool(f'scheduled_{i}') for i in range(n)]
    
    # Add constraints for each meeting
    for i in range(n):
        mtg = meetings[i]
        travel_from_richmond = get_travel_time('Richmond District', mtg['location'])
        # If scheduled, meeting must start after travel from Richmond and available start, end before available end, and have minimum duration
        opt.add(z3.Implies(scheduled[i], s[i] >= z3.Max(mtg['avail_start'], travel_from_richmond)))
        opt.add(z3.Implies(scheduled[i], e[i] <= mtg['avail_end']))
        opt.add(z3.Implies(scheduled[i], e[i] - s[i] >= mtg['min_dur']))
        opt.add(z3.Implies(scheduled[i], s[i] >= 0))
        opt.add(z3.Implies(scheduled[i], e[i] >= s[i]))
    
    # Add disjunctive constraints for every pair of meetings
    for i in range(n):
        for j in range(i+1, n):
            travel_ij = get_travel_time(meetings[i]['location'], meetings[j]['location'])
            travel_ji = get_travel_time(meetings[j]['location'], meetings[i]['location'])
            opt.add(z3.Implies(z3.And(scheduled[i], scheduled[j]),
                              z3.Or(s[i] >= e[j] + travel_ji, s[j] >= e[i] + travel_ij)))
    
    # Maximize the number of scheduled meetings
    opt.maximize(z3.Sum([z3.If(scheduled[i], 1, 0) for i in range(n)]))
    
    # Check and get the model
    if opt.check() == z3.sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if z3.is_true(model.eval(scheduled[i])):
                start_val = model.eval(s[i]).as_long()
                end_val = model.eval(e[i]).as_long()
                # Convert minutes from 9:00 AM to time string
                total_min_start = 540 + start_val  # 9:00 AM is 540 minutes from midnight
                total_min_end = 540 + end_val
                hours_start = total_min_start // 60
                minutes_start = total_min_start % 60
                hours_end = total_min_end // 60
                minutes_end = total_min_end % 60
                time_str_start = f"{hours_start}:{minutes_start:02d}"
                time_str_end = f"{hours_end}:{minutes_end:02d}"
                scheduled_meetings.append({
                    'action': 'meet',
                    'location': meetings[i]['location'],
                    'person': meetings[i]['name'],
                    'start_time': time_str_start,
                    'end_time': time_str_end
                })
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {'itinerary': scheduled_meetings}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()