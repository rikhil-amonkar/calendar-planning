# Define the busy times for Amanda and Nathan
amanda_busy_monday = [(9, 10.5), (11, 11.5), (12.5, 13), (13.5, 14), (14.5, 15)]
nathan_busy_monday = [(10, 10.5), (11, 11.5), (13.5, 14.5), (16, 16.5)]

amanda_busy_tuesday = [(9, 9.5), (10, 10.5), (11.5, 12), (13.5, 14.5), (15.5, 16.5), (16.5, 17)]
nathan_busy_tuesday = [(9, 10.5), (11, 13), (13.5, 14), (14.5, 15.5), (16, 16.5)]

# Function to check if a time slot is free
def is_free(busy_times, start, end):
    for b_start, b_end in busy_times:
        if start < b_end and end > b_start:
            return False
    return True

# Check Monday for Amanda (Nathan is not available)
for start in range(9, 17, 1):  # Check each hour from 9 to 16
    for minute in [0, 0.5]:  # Check each half-hour
        end = start + 0.5
        if start + 0.5 <= 17 and is_free(amanda_busy_monday, start, end):
            print(f"{int(start):02}:{int(minute*60):02}:{int(end):02}:{int((end-int(end))*60):02} Monday")
            exit()

# Check Tuesday for both Amanda and Nathan
for start in range(9, 11, 1):  # Check each hour from 9 to 10
    for minute in [0, 0.5]:  # Check each half-hour
        end = start + 0.5
        if start + 0.5 <= 11 and is_free(amanda_busy_tuesday, start, end) and is_free(nathan_busy_tuesday, start, end):
            print(f"{int(start):02}:{int(minute*60):02}:{int(end):02}:{int((end-int(end))*60):02} Tuesday")
            exit()