import json
from z3 import *

def main():
    friends = ['Amanda', 'Melissa', 'Jeffrey', 'Matthew', 'Nancy', 'Karen', 'Robert', 'Joseph']
    locations_of_friends = {
        'Amanda': 'Marina District',
        'Melissa': 'The Castro',
        'Jeffrey': 'Fisherman\'s Wharf',
        'Matthew': 'Bayview',
        'Nancy': 'Pacific Heights',
        'Karen': 'Mission District',
        'Robert': 'Alamo Square',
        'Joseph': 'Golden Gate Park'
    }
    
    availability = {
        'Amanda': (14*60+45 - 9*60, 19*60+30 - 9*60),  # 345 to 630 minutes
        'Melissa': (9*60+30 - 9*60, 17*60 - 9*60),      # 30 to 480 minutes
        'Jeffrey': (12*60+45 - 9*60, 18*60+45 - 9*60),  # 225 to 585 minutes
        'Matthew': (10*60+15 - 9*60, 13*60+15 - 9*60),  # 75 to 255 minutes
        'Nancy': (17*60 - 9*60, 21*60+30 - 9*60),       # 480 to 750 minutes
        'Karen': (17*60+30 - 9*60, 20*60+30 - 9*60),    # 510 to 690 minutes
        'Robert': (11*60+15 - 9*60, 17*60+30 - 9*60),   # 135 to 510 minutes
        'Joseph': (0, 21*60+15 - 9*60)                  # 0 to 735 minutes
    }
    
    min_time = {
        'Amanda': 105,
        'Melissa': 30,
        'Jeffrey': 120,
        'Matthew': 30,
        'Nancy': 105,
        'Karen': 105,
        'Robert': 120,
        'Joseph': 105
    }
    
    locations_list = ['Presidio', 'Marina District', 'The Castro', 'Fisherman\'s Wharf', 'Bayview', 
                      'Pacific Heights', 'Mission District', 'Alamo Square', 'Golden Gate Park']
    
    travel_dict = {loc: {} for loc in locations_list}
    
    travel_dict['Presidio']['Marina District'] = 11
    travel_dict['Presidio']['The Castro'] = 21
    travel_dict['Presidio']['Fisherman\'s Wharf'] = 19
    travel_dict['Presidio']['Bayview'] = 31
    travel_dict['Presidio']['Pacific Heights'] = 11
    travel_dict['Presidio']['Mission District'] = 26
    travel_dict['Presidio']['Alamo Square'] = 19
    travel_dict['Presidio']['Golden Gate Park'] = 12
    
    travel_dict['Marina District']['Presidio'] = 10
    travel_dict['Marina District']['The Castro'] = 22
    travel_dict['Marina District']['Fisherman\'s Wharf'] = 10
    travel_dict['Marina District']['Bayview'] = 27
    travel_dict['Marina District']['Pacific Heights'] = 7
    travel_dict['Marina District']['Mission District'] = 20
    travel_dict['Marina District']['Alamo Square'] = 15
    travel_dict['Marina District']['Golden Gate Park'] = 18
    
    travel_dict['The Castro']['Presidio'] = 20
    travel_dict['The Castro']['Marina District'] = 21
    travel_dict['The Castro']['Fisherman\'s Wharf'] = 24
    travel_dict['The Castro']['Bayview'] = 19
    travel_dict['The Castro']['Pacific Heights'] = 16
    travel_dict['The Castro']['Mission District'] = 7
    travel_dict['The Castro']['Alamo Square'] = 8
    travel_dict['The Castro']['Golden Gate Park'] = 11
    
    travel_dict['Fisherman\'s Wharf']['Presidio'] = 17
    travel_dict['Fisherman\'s Wharf']['Marina District'] = 9
    travel_dict['Fisherman\'s Wharf']['The Castro'] = 27
    travel_dict['Fisherman\'s Wharf']['Bayview'] = 26
    travel_dict['Fisherman\'s Wharf']['Pacific Heights'] = 12
    travel_dict['Fisherman\'s Wharf']['Mission District'] = 22
    travel_dict['Fisherman\'s Wharf']['Alamo Square'] = 21
    travel_dict['Fisherman\'s Wharf']['Golden Gate Park'] = 25
    
    travel_dict['Bayview']['Presidio'] = 32
    travel_dict['Bayview']['Marina District'] = 27
    travel_dict['Bayview']['The Castro'] = 19
    travel_dict['Bayview']['Fisherman\'s Wharf'] = 25
    travel_dict['Bayview']['Pacific Heights'] = 23
    travel_dict['Bayview']['Mission District'] = 13
    travel_dict['Bayview']['Alamo Square'] = 16
    travel_dict['Bayview']['Golden Gate Park'] = 22
    
    travel_dict['Pacific Heights']['Presidio'] = 11
    travel_dict['Pacific Heights']['Marina District'] = 6
    travel_dict['Pacific Heights']['The Castro'] = 16
    travel_dict['Pacific Heights']['Fisherman\'s Wharf'] = 13
    travel_dict['Pacific Heights']['Bayview'] = 22
    travel_dict['Pacific Heights']['Mission District'] = 15
    travel_dict['Pacific Heights']['Alamo Square'] = 10
    travel_dict['Pacific Heights']['Golden Gate Park'] = 15
    
    travel_dict['Mission District']['Presidio'] = 25
    travel_dict['Mission District']['Marina District'] = 19
    travel_dict['Mission District']['The Castro'] = 7
    travel_dict['Mission District']['Fisherman\'s Wharf'] = 22
    travel_dict['Mission District']['Bayview'] = 14
    travel_dict['Mission District']['Pacific Heights'] = 16
    travel_dict['Mission District']['Alamo Square'] = 11
    travel_dict['Mission District']['Golden Gate Park'] = 17
    
    travel_dict['Alamo Square']['Presidio'] = 17
    travel_dict['Alamo Square']['Marina District'] = 15
    travel_dict['Alamo Square']['The Castro'] = 8
    travel_dict['Alamo Square']['Fisherman\'s Wharf'] = 19
    travel_dict['Alamo Square']['Bayview'] = 16
    travel_dict['Alamo Square']['Pacific Heights'] = 10
    travel_dict['Alamo Square']['Mission District'] = 10
    travel_dict['Alamo Square']['Golden Gate Park'] = 9
    
    travel_dict['Golden Gate Park']['Presidio'] = 11
    travel_dict['Golden Gate Park']['Marina District'] = 16
    travel_dict['Golden Gate Park']['The Castro'] = 13
    travel_dict['Golden Gate Park']['Fisherman\'s Wharf'] = 24
    travel_dict['Golden Gate Park']['Bayview'] = 23
    travel_dict['Golden Gate Park']['Pacific Heights'] = 16
    travel_dict['Golden Gate Park']['Mission District'] = 17
    travel_dict['Golden Gate Park']['Alamo Square'] = 9
    
    s = Optimize()
    
    meets = {}
    starts = {}
    ends = {}
    for friend in friends:
        meets[friend] = Bool(f'meet_{friend}')
        starts[friend] = Int(f'start_{friend}')
        ends[friend] = Int(f'end_{friend}')
    
    for friend in friends:
        loc = locations_of_friends[friend]
        avail_start, avail_end = availability[friend]
        min_t = min_time[friend]
        s.add(Implies(meets[friend], 
                      And(starts[friend] >= avail_start,
                          ends[friend] <= avail_end,
                          ends[friend] >= starts[friend] + min_t,
                          starts[friend] >= 0)))
    
    for friend in friends:
        loc = locations_of_friends[friend]
        travel_time = travel_dict['Presidio'][loc]
        s.add(Implies(meets[friend], starts[friend] >= travel_time))
    
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            friend1 = friends[i]
            friend2 = friends[j]
            loc1 = locations_of_friends[friend1]
            loc2 = locations_of_friends[friend2]
            time1_to_2 = travel_dict[loc1][loc2]
            time2_to_1 = travel_dict[loc2][loc1]
            s.add(Implies(And(meets[friend1], meets[friend2]),
                          Or(ends[friend1] + time1_to_2 <= starts[friend2],
                             ends[friend2] + time2_to_1 <= starts[friend1])))
    
    num_meetings = Sum([If(meets[friend], 1, 0) for friend in friends])
    s.maximize(num_meetings)
    
    itinerary = []
    if s.check() == sat:
        model = s.model()
        schedule = []
        for friend in friends:
            if model.eval(meets[friend]):
                start_min = model.eval(starts[friend])
                end_min = model.eval(ends[friend])
                if is_int_value(start_min):
                    start_val = start_min.as_long()
                else:
                    start_val = int(str(start_min))
                if is_int_value(end_min):
                    end_val = end_min.as_long()
                else:
                    end_val = int(str(end_min))
                
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                
                schedule.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": start_time,
                    "end_time": end_time
                })
        schedule.sort(key=lambda x: (x['start_time'], x['end_time']))
        itinerary = schedule
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()