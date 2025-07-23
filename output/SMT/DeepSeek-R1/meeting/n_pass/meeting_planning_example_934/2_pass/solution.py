from z3 import *
import json

def main():
    friends = ['Mary', 'Kenneth', 'Joseph', 'Sarah', 'Thomas', 'Daniel', 'Richard', 'Mark', 'David', 'Karen']
    
    min_durations = {
        'Mary': 75,
        'Kenneth': 30,
        'Joseph': 120,
        'Sarah': 90,
        'Thomas': 15,
        'Daniel': 15,
        'Richard': 30,
        'Mark': 120,
        'David': 60,
        'Karen': 120
    }
    
    availability = {
        'Mary': ("8:00PM", "9:15PM"),
        'Kenneth': ("11:15AM", "7:15PM"),
        'Joseph': ("8:00PM", "10:00PM"),
        'Sarah': ("11:45AM", "2:30PM"),
        'Thomas': ("7:15PM", "7:45PM"),
        'Daniel': ("1:45PM", "8:30PM"),
        'Richard': ("8:00AM", "6:45PM"),
        'Mark': ("5:30PM", "9:30PM"),
        'David': ("8:00PM", "9:00PM"),
        'Karen': ("1:15PM", "6:30PM")
    }
    
    def time_to_minutes(time_str):
        time_str = time_str.strip().upper()
        if time_str.endswith('AM') or time_str.endswith('PM'):
            period = time_str[-2:]
            time_str_no_suffix = time_str[:-2].strip()
            parts = time_str_no_suffix.split(':')
            hour = int(parts[0])
            minute = int(parts[1]) if len(parts) >= 2 else 0
            if period == 'PM' and hour != 12:
                hour += 12
            if period == 'AM' and hour == 12:
                hour = 0
            total_minutes_since_midnight = hour * 60 + minute
            minutes_from_9am = total_minutes_since_midnight - (9 * 60)
            return minutes_from_9am
        else:
            parts = time_str.split(':')
            hour = int(parts[0])
            minute = int(parts[1]) if len(parts) >= 2 else 0
            total_minutes_since_midnight = hour * 60 + minute
            minutes_from_9am = total_minutes_since_midnight - (9 * 60)
            return minutes_from_9am

    travel_dict = {
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Russian Hill'): 8,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Russian Hill'): 18,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Russian Hill'): 13,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Russian Hill'): 4,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Russian Hill'): 7,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Russian Hill'): 8,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Marina District'): 7
    }
    
    friends_locations = {
        'Mary': 'Embarcadero',
        'Kenneth': 'The Castro',
        'Joseph': 'Haight-Ashbury',
        'Sarah': 'Union Square',
        'Thomas': 'North Beach',
        'Daniel': 'Pacific Heights',
        'Richard': 'Chinatown',
        'Mark': 'Golden Gate Park',
        'David': 'Marina District',
        'Karen': 'Russian Hill'
    }
    
    s = Optimize()
    
    meet_vars = {f: Bool(f'meet_{f}') for f in friends}
    start_vars = {f: Int(f'start_{f}') for f in friends}
    end_vars = {f: Int(f'end_{f}') for f in friends}
    
    for f in friends:
        start_avail = time_to_minutes(availability[f][0])
        end_avail = time_to_minutes(availability[f][1])
        effective_start_avail = If(start_avail < 0, 0, start_avail)
        loc = friends_locations[f]
        travel_from_nob = travel_dict[('Nob Hill', loc)]
        s.add(If(meet_vars[f],
                 And(
                     start_vars[f] >= travel_from_nob,
                     start_vars[f] >= effective_start_avail,
                     end_vars[f] == start_vars[f] + min_durations[f],
                     end_vars[f] <= end_avail,
                     start_vars[f] >= 0
                 ),
                 True))
    
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            if f1 == f2:
                continue
            loc1 = friends_locations[f1]
            loc2 = friends_locations[f2]
            t12 = travel_dict.get((loc1, loc2))
            t21 = travel_dict.get((loc2, loc1))
            if t12 is None or t21 is None:
                continue
            s.add(If(And(meet_vars[f1], meet_vars[f2]),
                     Or(end_vars[f1] + t12 <= start_vars[f2], 
                        end_vars[f2] + t21 <= start_vars[f1]),
                     True))
    
    s.maximize(Sum([If(meet_vars[f], 1, 0) for f in friends]))
    
    itinerary = []
    if s.check() == sat:
        m = s.model()
        for f in friends:
            if is_true(m.eval(meet_vars[f])):
                start_val = m.eval(start_vars[f])
                start_minutes = start_val.as_long()
                end_minutes = start_minutes + min_durations[f]
                total_minutes_start = start_minutes
                hours_start = 9 + total_minutes_start // 60
                minutes_start = total_minutes_start % 60
                start_time_str = f"{hours_start:02d}:{minutes_start:02d}"
                
                total_minutes_end = end_minutes
                hours_end = 9 + total_minutes_end // 60
                minutes_end = total_minutes_end % 60
                end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": f,
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
    else:
        itinerary = []
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == '__main__':
    main()