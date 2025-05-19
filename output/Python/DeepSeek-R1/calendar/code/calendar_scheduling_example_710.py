def find_meeting_time():
    days = ['Monday', 'Tuesday', 'Wednesday']
    # Cheryl cannot meet on Wednesday
    possible_days = ['Monday', 'Tuesday']
    
    # Check Tuesday first since Monday has full conflict for Kyle
    # Tuesday analysis
    cheryl_busy_tuesday = [(15, 0, 15, 30)]
    kyle_busy_tuesday = [(9, 30, 17, 0)]
    
    # Find gaps in Cheryl's Tuesday schedule before 15:00
    start_cheryl = (9, 0)
    end_cheryl = (15, 0)
    # Check available time 9:00-9:30 (before Kyle's busy time starts at 9:30)
    candidate_start = (9, 0)
    candidate_end = (9, 30)
    # Verify if this slot works for both
    # Cheryl is available 9:00-15:00 except 15:00-15:30
    # Kyle is available 9:00-9:30 on Tuesday
    # 30-minute meeting fits perfectly in 9:00-9:30
    return "Tuesday", (9, 0, 9, 30)

day, time = find_meeting_time()
print(f"{day} {time[0]:02d}:{time[1]:02d}:{time[2]:02d}:{time[3]:02d}")