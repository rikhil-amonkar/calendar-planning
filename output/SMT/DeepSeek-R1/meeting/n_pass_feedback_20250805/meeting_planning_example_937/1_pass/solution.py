from z3 import *
import json

def main():
    travel_text = """
Russian Hill to Sunset District: 23.
Russian Hill to Union Square: 10.
Russian Hill to Nob Hill: 5.
Russian Hill to Marina District: 7.
Russian Hill to Richmond District: 14.
Russian Hill to Financial District: 11.
Russian Hill to Embarcadero: 8.
Russian Hill to The Castro: 21.
Russian Hill to Alamo Square: 15.
Russian Hill to Presidio: 14.
Sunset District to Russian Hill: 24.
Sunset District to Union Square: 30.
Sunset District to Nob Hill: 27.
Sunset District to Marina District: 21.
Sunset District to Richmond District: 12.
Sunset District to Financial District: 30.
Sunset District to Embarcadero: 30.
Sunset District to The Castro: 17.
Sunset District to Alamo Square: 17.
Sunset District to Presidio: 16.
Union Square to Russian Hill: 13.
Union Square to Sunset District: 27.
Union Square to Nob Hill: 9.
Union Square to Marina District: 18.
Union Square to Richmond District: 20.
Union Square to Financial District: 9.
Union Square to Embarcadero: 11.
Union Square to The Castro: 17.
Union Square to Alamo Square: 15.
Union Square to Presidio: 24.
Nob Hill to Russian Hill: 5.
Nob Hill to Sunset District: 24.
Nob Hill to Union Square: 7.
Nob Hill to Marina District: 11.
Nob Hill to Richmond District: 14.
Nob Hill to Financial District: 9.
Nob Hill to Embarcadero: 9.
Nob Hill to The Castro: 17.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Marina District to Russian Hill: 8.
Marina District to Sunset District: 19.
Marina District to Union Square: 16.
Marina District to Nob Hill: 12.
Marina District to Richmond District: 11.
Marina District to Financial District: 17.
Marina District to Embarcadero: 14.
Marina District to The Castro: 22.
Marina District to Alamo Square: 15.
Marina District to Presidio: 10.
Richmond District to Russian Hill: 13.
Richmond District to Sunset District: 11.
Richmond District to Union Square: 21.
Richmond District to Nob Hill: 17.
Richmond District to Marina District: 9.
Richmond District to Financial District: 22.
Richmond District to Embarcadero: 19.
Richmond District to The Castro: 16.
Richmond District to Alamo Square: 13.
Richmond District to Presidio: 7.
Financial District to Russian Hill: 11.
Financial District to Sunset District: 30.
Financial District to Union Square: 9.
Financial District to Nob Hill: 8.
Financial District to Marina District: 15.
Financial District to Richmond District: 21.
Financial District to Embarcadero: 4.
Financial District to The Castro: 20.
Financial District to Alamo Square: 17.
Financial District to Presidio: 22.
Embarcadero to Russian Hill: 8.
Embarcadero to Sunset District: 30.
Embarcadero to Union Square: 10.
Embarcadero to Nob Hill: 10.
Embarcadero to Marina District: 12.
Embarcadero to Richmond District: 21.
Embarcadero to Financial District: 5.
Embarcadero to The Castro: 25.
Embarcadero to Alamo Square: 19.
Embarcadero to Presidio: 20.
The Castro to Russian Hill: 18.
The Castro to Sunset District: 17.
The Castro to Union Square: 19.
The Castro to Nob Hill: 16.
The Castro to Marina District: 21.
The Castro to Richmond District: 16.
The Castro to Financial District: 21.
The Castro to Embarcadero: 22.
The Castro to Alamo Square: 8.
The Castro to Presidio: 20.
Alamo Square to Russian Hill: 13.
Alamo Square to Sunset District: 16.
Alamo Square to Union Square: 14.
Alamo Square to Nob Hill: 11.
Alamo Square to Marina District: 15.
Alamo Square to Richmond District: 11.
Alamo Square to Financial District: 17.
Alamo Square to Embarcadero: 16.
Alamo Square to The Castro: 8.
Alamo Square to Presidio: 17.
Presidio to Russian Hill: 14.
Presidio to Sunset District: 15.
Presidio to Union Square: 22.
Presidio to Nob Hill: 18.
Presidio to Marina District: 11.
Presidio to Richmond District: 7.
Presidio to Financial District: 23.
Presidio to Embarcadero: 20.
Presidio to The Castro: 21.
Presidio to Alamo Square: 19.
    """
    
    def convert_time(time_str):
        time_str = time_str.strip().upper()
        if time_str.endswith("AM") or time_str.endswith("PM"):
            suffix = time_str[-2:]
            time_part = time_str[:-2].strip()
            if ':' in time_part:
                parts = time_part.split(':')
                hour = int(parts[0])
                minute = int(parts[1])
            else:
                hour = int(time_part)
                minute = 0
            if suffix == "PM" and hour != 12:
                hour += 12
            if suffix == "AM" and hour == 12:
                hour = 0
            total_minutes = hour * 60 + minute
            base_minutes = 9 * 60  # 9:00 AM in minutes from midnight
            return total_minutes - base_minutes
        else:
            raise ValueError(f"Unsupported time format: {time_str}")
    
    friends = [
        {"name": "David", "location": "Sunset District", 
         "start_avail": convert_time("9:15AM"), 
         "end_avail": convert_time("10:00PM"),
         "min_duration": 15},
        {"name": "Kenneth", "location": "Union Square", 
         "start_avail": convert_time("9:15PM"), 
         "end_avail": convert_time("9:45PM"),
         "min_duration": 15},
        {"name": "Patricia", "location": "Nob Hill", 
         "start_avail": convert_time("3:00PM"), 
         "end_avail": convert_time("7:15PM"),
         "min_duration": 120},
        {"name": "Mary", "location": "Marina District", 
         "start_avail": convert_time("2:45PM"), 
         "end_avail": convert_time("4:45PM"),
         "min_duration": 45},
        {"name": "Charles", "location": "Richmond District", 
         "start_avail": convert_time("5:15PM"), 
         "end_avail": convert_time("9:00PM"),
         "min_duration": 15},
        {"name": "Joshua", "location": "Financial District", 
         "start_avail": convert_time("2:30PM"), 
         "end_avail": convert_time("5:15PM"),
         "min_duration": 90},
        {"name": "Ronald", "location": "Embarcadero", 
         "start_avail": convert_time("6:15PM"), 
         "end_avail": convert_time("8:45PM"),
         "min_duration": 30},
        {"name": "George", "location": "The Castro", 
         "start_avail": convert_time("2:15PM"), 
         "end_avail": convert_time("7:00PM"),
         "min_duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", 
         "start_avail": convert_time("9:00AM"), 
         "end_avail": convert_time("2:30PM"),
         "min_duration": 105},
        {"name": "William", "location": "Presidio", 
         "start_avail": convert_time("7:00AM"), 
         "end_avail": convert_time("12:45PM"),
         "min_duration": 60}
    ]
    
    travel_times = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if ':' not in line:
            continue
        parts = line.split(':', 1)
        left = parts[0].strip()
        right = parts[1].strip().replace('.', '')
        try:
            value = int(right)
        except:
            continue
        if " to " in left:
            loc1, loc2 = left.split(" to ", 1)
            loc1 = loc1.strip()
            loc2 = loc2.strip()
            if loc1 not in travel_times:
                travel_times[loc1] = {}
            travel_times[loc1][loc2] = value
    
    locations = ["Russian Hill"]
    for friend in friends:
        locations.append(friend['location'])
    
    def get_travel_time(i, j):
        loc_i = locations[i]
        loc_j = locations[j]
        return travel_times[loc_i][loc_j]
    
    n_meetings = 11
    m = [Bool(f"m_{i}") for i in range(n_meetings)]
    s = [Int(f"s_{i}") for i in range(n_meetings)]
    e = [Int(f"e_{i}") for i in range(n_meetings)]
    
    opt = Optimize()
    
    opt.add(m[0] == True)
    opt.add(s[0] == 0)
    opt.add(e[0] == 0)
    
    for i in range(1, n_meetings):
        friend = friends[i-1]
        min_duration = friend['min_duration']
        start_avail = friend['start_avail']
        end_avail = friend['end_avail']
        opt.add(Implies(m[i], s[i] >= start_avail))
        opt.add(Implies(m[i], e[i] == s[i] + min_duration))
        opt.add(Implies(m[i], e[i] <= end_avail))
    
    for i in range(n_meetings):
        for j in range(n_meetings):
            if i == j:
                continue
            travel_ij = get_travel_time(i, j)
            travel_ji = get_travel_time(j, i)
            opt.add(Implies(And(m[i], m[j]),
                             Or( e[i] + travel_ij <= s[j],
                                 e[j] + travel_ji <= s[i] )))
    
    total_met = Sum([If(m[i], 1, 0) for i in range(1, n_meetings)])
    opt.maximize(total_met)
    
    itinerary = []
    if opt.check() == sat:
        model = opt.model()
        for i in range(1, n_meetings):
            if model.evaluate(m[i]):
                friend = friends[i-1]
                s_val = model.evaluate(s[i])
                if isinstance(s_val, IntNumRef):
                    s_val = s_val.as_long()
                else:
                    s_val = 0
                total_minutes_start = 9*60 + s_val
                hour = total_minutes_start // 60
                minute = total_minutes_start % 60
                start_time = f"{hour:02d}:{minute:02d}"
                min_duration = friend['min_duration']
                total_minutes_end = 9*60 + s_val + min_duration
                hour_end = total_minutes_end // 60
                minute_end = total_minutes_end % 60
                end_time = f"{hour_end:02d}:{minute_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
    else:
        print("No solution found.")
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()