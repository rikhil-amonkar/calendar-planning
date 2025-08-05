from z3 import *
import json

def main():
    # Initialize travel_dict from provided data
    travel_dict = {}
    locations = [
        'Pacific Heights', 'Golden Gate Park', 'The Castro', 'Bayview', 'Marina District',
        'Union Square', 'Sunset District', 'Alamo Square', 'Financial District', 'Mission District'
    ]
    for loc in locations:
        travel_dict[loc] = {}
    
    data = """
    Pacific Heights to Golden Gate Park: 15.
    Pacific Heights to The Castro: 16.
    Pacific Heights to Bayview: 22.
    Pacific Heights to Marina District: 6.
    Pacific Heights to Union Square: 12.
    Pacific Heights to Sunset District: 21.
    Pacific Heights to Alamo Square: 10.
    Pacific Heights to Financial District: 13.
    Pacific Heights to Mission District: 15.
    Golden Gate Park to Pacific Heights: 16.
    Golden Gate Park to The Castro: 13.
    Golden Gate Park to Bayview: 23.
    Golden Gate Park to Marina District: 16.
    Golden Gate Park to Union Square: 22.
    Golden Gate Park to Sunset District: 10.
    Golden Gate Park to Alamo Square: 9.
    Golden Gate Park to Financial District: 26.
    Golden Gate Park to Mission District: 17.
    The Castro to Pacific Heights: 16.
    The Castro to Golden Gate Park: 11.
    The Castro to Bayview: 19.
    The Castro to Marina District: 21.
    The Castro to Union Square: 19.
    The Castro to Sunset District: 17.
    The Castro to Alamo Square: 8.
    The Castro to Financial District: 21.
    The Castro to Mission District: 7.
    Bayview to Pacific Heights: 23.
    Bayview to Golden Gate Park: 22.
    Bayview to The Castro: 19.
    Bayview to Marina District: 27.
    Bayview to Union Square: 18.
    Bayview to Sunset District: 23.
    Bayview to Alamo Square: 16.
    Bayview to Financial District: 19.
    Bayview to Mission District: 13.
    Marina District to Pacific Heights: 7.
    Marina District to Golden Gate Park: 18.
    Marina District to The Castro: 22.
    Marina District to Bayview: 27.
    Marina District to Union Square: 16.
    Marina District to Sunset District: 19.
    Marina District to Alamo Square: 15.
    Marina District to Financial District: 17.
    Marina District to Mission District: 20.
    Union Square to Pacific Heights: 15.
    Union Square to Golden Gate Park: 22.
    Union Square to The Castro: 17.
    Union Square to Bayview: 15.
    Union Square to Marina District: 18.
    Union Square to Sunset District: 27.
    Union Square to Alamo Square: 15.
    Union Square to Financial District: 9.
    Union Square to Mission District: 14.
    Sunset District to Pacific Heights: 21.
    Sunset District to Golden Gate Park: 11.
    Sunset District to The Castro: 17.
    Sunset District to Bayview: 22.
    Sunset District to Marina District: 21.
    Sunset District to Union Square: 30.
    Sunset District to Alamo Square: 17.
    Sunset District to Financial District: 30.
    Sunset District to Mission District: 25.
    Alamo Square to Pacific Heights: 10.
    Alamo Square to Golden Gate Park: 9.
    Alamo Square to The Castro: 8.
    Alamo Square to Bayview: 16.
    Alamo Square to Marina District: 15.
    Alamo Square to Union Square: 14.
    Alamo Square to Sunset District: 16.
    Alamo Square to Financial District: 17.
    Alamo Square to Mission District: 10.
    Financial District to Pacific Heights: 13.
    Financial District to Golden Gate Park: 23.
    Financial District to The Castro: 20.
    Financial District to Bayview: 19.
    Financial District to Marina District: 15.
    Financial District to Union Square: 9.
    Financial District to Sunset District: 30.
    Financial District to Alamo Square: 17.
    Financial District to Mission District: 17.
    Mission District to Pacific Heights: 16.
    Mission District to Golden Gate Park: 17.
    Mission District to The Castro: 7.
    Mission District to Bayview: 14.
    Mission District to Marina District: 19.
    Mission District to Union Square: 15.
    Mission District to Sunset District: 24.
    Mission District to Alamo Square: 11.
    Mission District to Financial District: 15.
    """
    lines = data.strip().split('\n')
    for line in lines:
        if not line.strip():
            continue
        parts = line.split(':')
        if len(parts) < 2:
            continue
        time_str = parts[1].strip().rstrip('.').strip()
        try:
            time_val = int(time_str)
        except:
            continue
        from_to = parts[0].split(' to ')
        if len(from_to) < 2:
            continue
        from_loc = from_to[0].strip()
        to_loc = from_to[1].strip()
        travel_dict[from_loc][to_loc] = time_val

    # Meeting indices and their locations
    meeting_index_to_person = {
        1: 'Helen',
        2: 'Steven',
        3: 'Deborah',
        4: 'Matthew',
        5: 'Joseph',
        6: 'Ronald',
        7: 'Robert',
        8: 'Rebecca',
        9: 'Elizabeth'
    }
    meeting_index_to_location = {
        1: 'Golden Gate Park',
        2: 'The Castro',
        3: 'Bayview',
        4: 'Marina District',
        5: 'Union Square',
        6: 'Sunset District',
        7: 'Alamo Square',
        8: 'Financial District',
        9: 'Mission District'
    }

    # Time constraints in minutes since midnight (9:00 AM is 540 minutes)
    available_start = {
        1: 570,    # Helen: 9:30 AM
        2: 1215,   # Steven: 8:15 PM (20:15) = 20*60+15 = 1215
        3: 510,    # Deborah: 8:30 AM = 8*60+30 = 510 (but note: we start at 9:00, so effective start is after travel)
        4: 555,    # Matthew: 9:15 AM = 9*60+15 = 555
        5: 855,    # Joseph: 2:15 PM = 14*60+15 = 855
        6: 960,    # Ronald: 4:00 PM = 16*60 = 960
        7: 1110,   # Robert: 6:30 PM = 18*60+30 = 1110
        8: 885,    # Rebecca: 2:45 PM = 14*60+45 = 885
        9: 1110    # Elizabeth: 6:30 PM = 18*60+30 = 1110
    }
    available_end = {
        1: 735,    # Helen: 12:15 PM = 12*60+15 = 735
        2: 1320,   # Steven: 10:00 PM = 22*60 = 1320
        3: 720,    # Deborah: 12:00 PM = 12*60 = 720
        4: 855,    # Matthew: 2:15 PM = 14*60+15 = 855
        5: 1125,   # Joseph: 6:45 PM = 18*60+45 = 1125
        6: 1245,   # Ronald: 8:45 PM = 20*60+45 = 1245
        7: 1275,   # Robert: 9:15 PM = 21*60+15 = 1275
        8: 975,    # Rebecca: 4:15 PM = 16*60+15 = 975
        9: 1260    # Elizabeth: 9:00 PM = 21*60 = 1260
    }
    min_duration = {
        1: 45,
        2: 105,
        3: 30,
        4: 45,
        5: 120,
        6: 60,
        7: 120,
        8: 30,
        9: 120
    }

    # Initialize Z3 solver and variables
    s = Optimize()
    b = {}
    pos = {}
    start = {}
    end = {}
    for i in range(1, 10):
        b[i] = Bool(f'b_{i}')
        pos[i] = Int(f'pos_{i}')
        start[i] = Int(f'start_{i}')
        end[i] = Int(f'end_{i}')

    # Dummy start at Pacific Heights
    start0 = 540
    end0 = 540

    # Constraints for each meeting
    for i in range(1, 10):
        s.add(If(b[i],
                 And(
                     start[i] >= available_start[i],
                     end[i] <= available_end[i],
                     end[i] - start[i] >= min_duration[i]
                 ),
                 True))
        s.add(If(b[i], And(pos[i] >= 1, pos[i] <= 9), True))

    # Distinct positions for active meetings
    for i in range(1, 10):
        for j in range(i+1, 10):
            s.add(If(And(b[i], b[j]), pos[i] != pos[j], True))

    # Travel constraints: from start0 to first meeting
    for i in range(1, 10):
        s.add(If(And(b[i], pos[i] == 1),
                 start[i] >= start0 + travel_dict['Pacific Heights'][meeting_index_to_location[i]],
                 True))

    # Travel constraints between consecutive meetings
    for i in range(1, 10):
        for j in range(1, 10):
            if i == j:
                continue
            s.add(If(And(b[i], b[j], pos[i] == pos[j] + 1),
                     end[j] + travel_dict[meeting_index_to_location[j]][meeting_index_to_location[i]] <= start[i],
                     True))

    # Ensure active meetings have consecutive positions starting from 1
    M = Sum([If(b_i, 1, 0) for b_i in [b[i] for i in range(1,10)]])
    for k in range(1, 10):
        s.add(If(M >= k,
                 Or([And(b[i], pos[i] == k) for i in range(1, 10)]),
                 True))

    # Maximize the number of meetings
    s.maximize(Sum([If(b_i, 1, 0) for b_i in [b[i] for i in range(1,10)]]))

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        active_meetings = []
        for i in range(1, 10):
            if model.evaluate(b[i]):
                start_val = model.evaluate(start[i])
                end_val = model.evaluate(end[i])
                if isinstance(start_val, IntNumRef) and isinstance(end_val, IntNumRef):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    pos_val = model.evaluate(pos[i]).as_long()
                    active_meetings.append({
                        'person': meeting_index_to_person[i],
                        'start_min': start_min,
                        'end_min': end_min,
                        'position': pos_val
                    })
        # Sort by position
        active_meetings.sort(key=lambda x: x['position'])
        itinerary = []
        for meeting in active_meetings:
            # Convert minutes since midnight to HH:MM
            start_hour = meeting['start_min'] // 60
            start_minute = meeting['start_min'] % 60
            end_hour = meeting['end_min'] // 60
            end_minute = meeting['end_min'] % 60
            start_time = f"{start_hour:02d}:{start_minute:02d}"
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": meeting['person'],
                "start_time": start_time,
                "end_time": end_time
            })
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("SOLUTION:")
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()