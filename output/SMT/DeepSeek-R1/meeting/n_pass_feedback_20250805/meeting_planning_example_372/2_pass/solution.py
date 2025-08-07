from z3 import *

def main():
    # Travel time matrix: 0=Sunset, 1=Alamo, 2=Russian, 3=Golden, 4=Mission
    T = [
        [0, 17, 24, 11, 24],   # from Sunset (0)
        [16, 0, 13, 9, 10],    # from Alamo (1)
        [23, 15, 0, 21, 16],   # from Russian (2)
        [10, 10, 19, 0, 17],   # from Golden (3)
        [24, 11, 15, 17, 0]    # from Mission (4)
    ]
    
    opt = Optimize()
    
    # Boolean variables for each meeting
    meet1 = Bool('meet1')  # Charles at Alamo (1)
    meet2 = Bool('meet2')  # Margaret at Russian (2)
    meet3 = Bool('meet3')  # Daniel at Golden (3)
    meet4 = Bool('meet4')  # Stephanie at Mission (4)
    
    # Start time variables (in minutes from midnight)
    start1 = Int('start1')
    start2 = Int('start2')
    start3 = Int('start3')
    start4 = Int('start4')
    
    # Durations in minutes
    duration1 = 90  # Charles
    duration2 = 30  # Margaret
    duration3 = 15  # Daniel
    duration4 = 90  # Stephanie
    
    # End times
    end1 = start1 + duration1
    end2 = start2 + duration2
    end3 = start3 + duration3
    end4 = start4 + duration4
    
    # Constraints for each meeting if scheduled
    # Charles: available 1080 (6PM) to 1245 (8:45PM), min 90 min -> must start by 1155 (1155+90=1245)
    opt.add(Implies(meet1, And(start1 >= 1080, end1 <= 1245, start1 <= 1155)))
    # Margaret: available 540 (9AM) to 960 (4PM), min 30 min -> must start by 930 (930+30=960)
    # But also must account for travel from start (Sunset) to Russian: 24 min -> start2 >= 540+24=564
    opt.add(Implies(meet2, And(start2 >= 564, end2 <= 960, start2 <= 930)))
    # Daniel: available 480 (8AM) to 810 (1:30PM), min 15 min -> must start by 795 (795+15=810)
    # Travel from Sunset to Golden: 11 min -> start3 >= 540+11=551
    opt.add(Implies(meet3, And(start3 >= 551, end3 <= 810, start3 <= 795)))
    # Stephanie: available 1230 (8:30PM) to 1320 (10PM), min 90 min -> must start at 1230 (1230+90=1320)
    opt.add(Implies(meet4, And(start4 == 1230, end4 == 1320)))
    
    # Pairwise constraints for every pair of meetings (if both are scheduled)
    # Charles (1) and Margaret (2)
    opt.add(Implies(And(meet1, meet2), 
                   Or(end1 + T[1][2] <= start2, end2 + T[2][1] <= start1)))
    # Charles (1) and Daniel (3)
    opt.add(Implies(And(meet1, meet3), 
                   Or(end1 + T[1][3] <= start3, end3 + T[3][1] <= start1)))
    # Charles (1) and Stephanie (4)
    opt.add(Implies(And(meet1, meet4), 
                   Or(end1 + T[1][4] <= start4, end4 + T[4][1] <= start1)))
    # Margaret (2) and Daniel (3)
    opt.add(Implies(And(meet2, meet3), 
                   Or(end2 + T[2][3] <= start3, end3 + T[3][2] <= start2)))
    # Margaret (2) and Stephanie (4)
    opt.add(Implies(And(meet2, meet4), 
                   Or(end2 + T[2][4] <= start4, end4 + T[4][2] <= start2)))
    # Daniel (3) and Stephanie (4)
    opt.add(Implies(And(meet3, meet4), 
                   Or(end3 + T[3][4] <= start4, end4 + T[4][3] <= start3)))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet1, 1, 0), If(meet2, 1, 0), If(meet3, 1, 0), If(meet4, 1, 0)])
    opt.maximize(total_meetings)
    
    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        meetings = []
        # Check which meetings are scheduled and collect their details
        if is_true(m[meet1]):
            s1 = m.evaluate(start1).as_long()
            meetings.append(("Charles", s1, s1 + duration1))
        if is_true(m[meet2]):
            s2 = m.evaluate(start2).as_long()
            meetings.append(("Margaret", s2, s2 + duration2))
        if is_true(m[meet3]):
            s3 = m.evaluate(start3).as_long()
            meetings.append(("Daniel", s3, s3 + duration3))
        if is_true(m[meet4]):
            meetings.append(("Stephanie", 1230, 1320))
        
        # Convert times to HH:MM and sort by start time
        formatted_meetings = []
        for person, start_min, end_min in meetings:
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            formatted_meetings.append({
                "action": "meet", 
                "person": person, 
                "start_time": start_str, 
                "end_time": end_str
            })
        formatted_meetings.sort(key=lambda x: x['start_time'])
        result = {"itinerary": formatted_meetings}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()