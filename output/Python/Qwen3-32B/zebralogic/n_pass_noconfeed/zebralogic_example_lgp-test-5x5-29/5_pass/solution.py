edus_list = [
    ['Alice', 25, 'bachelor'],
    ['Bob', 30, 'master'],
    ['Charlie', 22, 'bachelor']
]

for edus_p in edus_list:
    if edus_p[2] != 'bachelor':
        continue
    print(f"Processing: {edus_p[0]}")