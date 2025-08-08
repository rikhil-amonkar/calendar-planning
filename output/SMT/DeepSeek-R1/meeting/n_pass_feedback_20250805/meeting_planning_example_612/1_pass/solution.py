from z3 import *

def main():
    # Define travel_time_dict from the given data
    travel_time_dict = {
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Embarcadero'): 31,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Embarcadero'): 25
    }

    friends = [
        ('Emily', 'Russian Hill', (12*60+15, 14*60+15), 105),  # 12:15PM to 2:15PM
        ('Mark', 'Presidio', (14*60+45, 19*60+30), 60),        # 2:45PM to 7:30PM
        ('Deborah', 'Chinatown', (7*60+30, 15*60+30), 45),     # 7:30AM to 3:30PM
        ('Margaret', 'Sunset District', (21*60+30, 22*60+30), 60),  # 9:30PM to 10:30PM
        ('George', 'The Castro', (7*60+30, 14*60+15), 60),     # 7:30AM to 2:15PM
        ('Andrew', 'Embarcadero', (20*60+15, 22*60+00), 75),  # 8:15PM to 10:00PM
        ('Steven', 'Golden Gate Park', (11*60+15, 21*60+15), 105)  # 11:15AM to 9:15PM
    ]

    n = len(friends)
    s = Optimize()

    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    end = [Real(f'end_{i}') for i in range(n)]

    before = [[Bool(f'before_{i}_{j}') for j in range(n)] for i in range(n)]

    available_start = []
    available_end = []
    min_duration = []
    locations = []
    for i, (name, loc, (s_start, s_end), dur) in enumerate(friends):
        available_start.append(s_start)
        available_end.append(s_end)
        min_duration.append(dur)
        locations.append(loc)

    for i in range(n):
        s.add(Implies(meet[i], start[i] >= available_start[i]))
        s.add(Implies(meet[i], end[i] == start[i] + min_duration[i]))
        s.add(Implies(meet[i], end[i] <= available_end[i]))

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            s.add(Implies(And(meet[i], meet[j]), before[i][j] == Not(before[j][i])))
            tt = travel_time_dict.get((locations[i], locations[j]), 10000)
            s.add(Implies(And(meet[i], meet[j], before[i][j]), end[i] + tt <= start[j]))

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for k in range(n):
                if i == k or j == k:
                    continue
                s.add(Implies(And(meet[i], meet[j], meet[k], before[i][j], before[j][k]), before[i][k]))

    for i in range(n):
        conditions = []
        for j in range(n):
            if i == j:
                continue
            conditions.append(Implies(meet[j], before[i][j]))
        first_i = And(conditions)
        tt = travel_time_dict.get(('Alamo Square', locations[i]), 10000)
        s.add(Implies(And(meet[i], first_i), start[i] >= 540 + tt))

    objective = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(objective)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            if is_true(m.eval(meet[i])):
                start_val = m.eval(start[i])
                end_val = m.eval(end[i])
                try:
                    start_minutes = float(start_val.numerator_as_long())/float(start_val.denominator_as_long())
                except:
                    start_minutes = float(start_val.as_long())
                try:
                    end_minutes = float(end_val.numerator_as_long())/float(end_val.denominator_as_long())
                except:
                    end_minutes = float(end_val.as_long())
                start_minutes = round(start_minutes)
                end_minutes = round(end_minutes)
                start_hh = int(start_minutes) // 60
                start_mm = int(start_minutes) % 60
                end_hh = int(end_minutes) // 60
                end_mm = int(end_minutes) % 60
                start_time = f"{start_hh:02d}:{start_mm:02d}"
                end_time = f"{end_hh:02d}:{end_mm:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i][0],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary_sorted = sorted(itinerary, key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
        print(f"SOLUTION: {{\"itinerary\": {itinerary_sorted}}}")
    else:
        print("SOLUTION: {\"itinerary\": []}")

if __name__ == '__main__':
    main()