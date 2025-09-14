from z3 import Int, Bool, If, Optimize, sat
import json

def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    
    # Define meeting start and end time variables (in minutes from midnight)
    s_kev, e_kev = Int('s_kev'), Int('e_kev')
    s_kim, e_kim = Int('s_kim'), Int('e_kim')
    s_jos, e_jos = Int('s_jos'), Int('e_jos')
    s_tho, e_tho = Int('s_tho'), Int('e_tho')
    
    # Boolean to decide morning meeting order
    # True  => Kevin is met first (at Alamo Square), then Kimberly (at Russian Hill)
    # False => Kimberly is met first, then Kevin
    order_morning = Bool('order_morning')
    
    # -------------------------------
    # Duration constraints for each meeting
    # Kevin requires at least 75 minutes.
    opt.add(e_kev - s_kev >= 75)
    # Kimberly requires at least 30 minutes.
    opt.add(e_kim - s_kim >= 30)
    # Joseph requires at least 45 minutes.
    opt.add(e_jos - s_jos >= 45)
    # Thomas requires at least 45 minutes.
    opt.add(e_tho - s_tho >= 45)
    
    # -------------------------------
    # Availability constraints for each friend (times in minutes from midnight)
    # Kevin is at Alamo Square from 8:15 (495) to 21:30 (1290)
    opt.add(s_kev >= 495, e_kev <= 1290)
    # Kimberly is at Russian Hill from 8:45 (525) to 12:30 (750)
    opt.add(s_kim >= 525, e_kim <= 750)
    # Joseph is at Presidio from 18:30 (1110) to 19:15 (1155)
    opt.add(s_jos >= 1110, e_jos <= 1155)
    # Thomas is at Financial District from 19:00 (1140) to 21:45 (1305)
    opt.add(s_tho >= 1140, e_tho <= 1305)
    
    # -------------------------------
    # Travel time constants (in minutes)
    # From initial location (Sunset District at 9:00 which is 540 minutes) to:
    # Alamo Square: 17 minutes, Russian Hill: 24 minutes.
    # Between morning meeting locations:
    #   Alamo Square -> Russian Hill: 13 minutes
    #   Russian Hill -> Alamo Square: 15 minutes
    # From morning meeting finish to Joseph's location (Presidio):
    #   From Russian Hill: 14 minutes, From Alamo Square: 18 minutes
    # From Joseph's location (Presidio) to Thomas' location (Financial District): 23 minutes
    
    # Morning travel constraints depending on order:
    # If Kevin is first then:
    #   - Kevin meeting must start after traveling from Sunset District to Alamo Square: 540 + 17 = 557.
    #   - Kimberly meeting (second) must start after Kevin's end plus travel from Alamo Square to Russian Hill: +13 minutes.
    # If Kimberly is first then:
    #   - Kimberly meeting must start after traveling from Sunset District to Russian Hill: 540 + 24 = 564.
    #   - Kevin meeting (second) must start after Kimberly's end plus travel from Russian Hill to Alamo Square: +15 minutes.
    opt.add(If(order_morning, s_kev >= 540 + 17, s_kim >= 540 + 24))
    opt.add(If(order_morning, s_kim >= e_kev + 13, s_kev >= e_kim + 15))
    
    # Transition from morning meetings to Joseph's meeting:
    # If Kevin was first then Kimberly is the second meeting at Russian Hill and travel to Presidio takes 14 minutes.
    # If Kimberly was first then Kevin is the second meeting at Alamo Square and travel to Presidio takes 18 minutes.
    opt.add(s_jos >= If(order_morning, e_kim + 14, e_kev + 18))
    
    # Transition from Joseph to Thomas meeting:
    # Must allow travel from Presidio to Financial District: 23 minutes.
    opt.add(s_tho >= e_jos + 23)
    
    # -------------------------------
    # Objective: Minimize the finish time of Thomas meeting (to get an 'optimal' schedule)
    opt.minimize(e_tho)
    
    if opt.check() == sat:
        model = opt.model()
        # Extract computed meeting times
        s_kev_val = model[s_kev].as_long()
        e_kev_val = model[e_kev].as_long()
        s_kim_val = model[s_kim].as_long()
        e_kim_val = model[e_kim].as_long()
        s_jos_val = model[s_jos].as_long()
        e_jos_val = model[e_jos].as_long()
        s_tho_val = model[s_tho].as_long()
        e_tho_val = model[e_tho].as_long()
        order_val = model.evaluate(order_morning)
        
        itinerary = []
        # Build morning itinerary based on the ordering decision.
        if order_val:
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "Kevin",
                "start_time": minutes_to_str(s_kev_val),
                "end_time": minutes_to_str(e_kev_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Kimberly",
                "start_time": minutes_to_str(s_kim_val),
                "end_time": minutes_to_str(e_kim_val)
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Kimberly",
                "start_time": minutes_to_str(s_kim_val),
                "end_time": minutes_to_str(e_kim_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "Kevin",
                "start_time": minutes_to_str(s_kev_val),
                "end_time": minutes_to_str(e_kev_val)
            })
        
        # Add evening meetings (order is fixed based on friend availability)
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Joseph",
            "start_time": minutes_to_str(s_jos_val),
            "end_time": minutes_to_str(e_jos_val)
        })
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Thomas",
            "start_time": minutes_to_str(s_tho_val),
            "end_time": minutes_to_str(e_tho_val)
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()