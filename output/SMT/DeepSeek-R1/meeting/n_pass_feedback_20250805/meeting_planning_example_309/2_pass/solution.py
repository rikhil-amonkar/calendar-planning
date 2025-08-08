from z3 import *
import json

def main():
    # Convert times to minutes since 9:00 AM
    nancy_avail_start = 30  # 9:30 AM
    nancy_avail_end = 270   # 1:30 PM
    mary_avail_start = 0     # 9:00 AM
    mary_avail_end = 720     # 9:00 PM
    jessica_avail_start = 135 # 11:15 AM
    jessica_avail_end = 285   # 1:45 PM

    nancy_dur = 90
    mary_dur = 75
    jessica_dur = 45

    travel_dict = {
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
        ('Chinatown', 'Chinatown'): 0,
        ('Alamo Square', 'Alamo Square'): 0,
        ('Bayview', 'Bayview'): 0
    }

    loc_map = {
        "Nancy": "Chinatown",
        "Mary": "Alamo Square",
        "Jessica": "Bayview"
    }

    s = Optimize()

    # Boolean variables for whether we meet each friend
    do_Nancy = Bool('do_Nancy')
    do_Mary = Bool('do_Mary')
    do_Jessica = Bool('do_Jessica')

    # Integer variables for start times (in minutes since 9:00 AM)
    start_Nancy = Int('start_Nancy')
    start_Mary = Int('start_Mary')
    start_Jessica = Int('start_Jessica')

    # End times are derived
    end_Nancy = start_Nancy + nancy_dur
    end_Mary = start_Mary + mary_dur
    end_Jessica = start_Jessica + jessica_dur

    # Constraints for Nancy
    s.add(Implies(do_Nancy, start_Nancy >= nancy_avail_start))
    s.add(Implies(do_Nancy, end_Nancy <= nancy_avail_end))
    s.add(Implies(do_Nancy, start_Nancy >= travel_dict[('Financial District', loc_map["Nancy"])]))

    # Constraints for Mary
    s.add(Implies(do_Mary, start_Mary >= mary_avail_start))
    s.add(Implies(do_Mary, end_Mary <= mary_avail_end))
    s.add(Implies(do_Mary, start_Mary >= travel_dict[('Financial District', loc_map["Mary"])]))

    # Constraints for Jessica
    s.add(Implies(do_Jessica, start_Jessica >= jessica_avail_start))
    s.add(Implies(do_Jessica, end_Jessica <= jessica_avail_end))
    s.add(Implies(do_Jessica, start_Jessica >= travel_dict[('Financial District', loc_map["Jessica"])]))

    # Pairwise constraints for overlapping meetings
    # Nancy and Mary
    s.add(Implies(And(do_Nancy, do_Mary),
                 Or(
                     end_Nancy + travel_dict[(loc_map["Nancy"], loc_map["Mary"])] <= start_Mary,
                     end_Mary + travel_dict[(loc_map["Mary"], loc_map["Nancy"])] <= start_Nancy
                 )))
    # Nancy and Jessica
    s.add(Implies(And(do_Nancy, do_Jessica),
                 Or(
                     end_Nancy + travel_dict[(loc_map["Nancy"], loc_map["Jessica"])] <= start_Jessica,
                     end_Jessica + travel_dict[(loc_map["Jessica"], loc_map["Nancy"])] <= start_Nancy
                 )))
    # Mary and Jessica
    s.add(Implies(And(do_Mary, do_Jessica),
                 Or(
                     end_Mary + travel_dict[(loc_map["Mary"], loc_map["Jessica"])] <= start_Jessica,
                     end_Jessica + travel_dict[(loc_map["Jessica"], loc_map["Mary"])] <= start_Mary
                 )))

    # Start times must be non-negative
    s.add(Implies(do_Nancy, start_Nancy >= 0))
    s.add(Implies(do_Mary, start_Mary >= 0))
    s.add(Implies(do_Jessica, start_Jessica >= 0))

    # Objective: maximize the number of meetings
    num_meetings = If(do_Nancy, 1, 0) + If(do_Mary, 1, 0) + If(do_Jessica, 1, 0)
    s.maximize(num_meetings)

    # Solve and extract solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        def min_to_time(total_min):
            hours = 9 + total_min // 60
            minutes = total_min % 60
            return f"{hours:02d}:{minutes:02d}"
        
        if model.eval(do_Nancy):
            start_val = model.eval(start_Nancy)
            if is_int_value(start_val):
                start_min = start_val.as_long()
                end_min = start_min + nancy_dur
                start_time_str = min_to_time(start_min)
                end_time_str = min_to_time(end_min)
                itinerary.append({"action": "meet", "person": "Nancy", "start_time": start_time_str, "end_time": end_time_str})
        
        if model.eval(do_Mary):
            start_val = model.eval(start_Mary)
            if is_int_value(start_val):
                start_min = start_val.as_long()
                end_min = start_min + mary_dur
                start_time_str = min_to_time(start_min)
                end_time_str = min_to_time(end_min)
                itinerary.append({"action": "meet", "person": "Mary", "start_time": start_time_str, "end_time": end_time_str})
        
        if model.eval(do_Jessica):
            start_val = model.eval(start_Jessica)
            if is_int_value(start_val):
                start_min = start_val.as_long()
                end_min = start_min + jessica_dur
                start_time_str = min_to_time(start_min)
                end_time_str = min_to_time(end_min)
                itinerary.append({"action": "meet", "person": "Jessica", "start_time": start_time_str, "end_time": end_time_str})
        
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()