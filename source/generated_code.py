participants = [
    {"name": "Heather", "blocked": [(9, 9.5), (10.5, 11), (13, 14), (14.5, 15), (16, 16.5)]},
    {"name": "Nicholas", "blocked": []},
    {"name": "Zachary", "blocked": [(9, 10.5), (11, 12), (12.5, 13), (13.5, 16.5)], "preferences": [(14, 14.5)]}
]

for start in range(9, 17):
    for participant in participants:
        overlap = False
        for block in participant["blocked"]:
            block_start = block[0] * 60
            block_end = block[1] * 60
            meeting_start = start * 60
            meeting_end = (start + 0.5) * 60
            if meeting_start < block_end and meeting_end > block_start:
                overlap = True
                break
        if not overlap and (start not in participant.get("preferences", [])):
            print(f"{start:02d}:{start:02d}:{start + 0.5:02d}:{start + 0.5:02d}")
            exit()