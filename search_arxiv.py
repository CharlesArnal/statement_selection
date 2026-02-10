import time
from datetime import timedelta

from sickle import Sickle

# --- CONFIGURATION ---
TIMEOUT_MINUTES = 5
FROM_DATE = '2023-01-01'  # Looking for recent papers
SUBJECT_SET = 'math'      # Change to 'cs' or 'physics' if desired
LICENSE_FILTER = "creativecommons.org/licenses/by/4.0" # Target License

# Keywords to find textbooks
KEYWORDS = [
    "textbook", "lecture notes", "course notes", 
    "introduction to", "comprehensive survey", 
    "graduate course", "undergraduate course",
    "tutorial", "monograph"
]

OUTPUT_FILE = f'arxiv_recent_textbooks_{SUBJECT_SET}.md'
# ---------------------

def run_harvester():
    sickle = Sickle('https://oaipmh.arxiv.org/oai')
    start_time = time.time()
    end_time = start_time + (TIMEOUT_MINUTES * 60)

    print("--- STARTING HARVEST ---")
    print(f"Subject: {SUBJECT_SET}")
    print(f"From:    {FROM_DATE}")
    
    try:
        records = sickle.ListRecords(**{
            'metadataPrefix': 'arXiv',
            'set': SUBJECT_SET,
            'from': FROM_DATE,
        })
    except Exception as e:
        print(f"Connection Error: {e}")
        return

    matches = 0
    scanned = 0

    with open(OUTPUT_FILE, mode='w', encoding='utf-8') as f:
        f.write('| ID | Title | Authors | License | Link |\n')
        f.write('| -- | ----- | ------- | ------- | ---- |\n')
        f.flush()

        print("\nScanning... (Press Ctrl+C to stop early)")
        
        try:
            for record in records:
                scanned += 1
                
                # Skip deleted records
                if record.header.deleted:
                    continue

                if time.time() > end_time:
                    print("\n[!] Timeout reached.")
                    break

                meta = record.metadata
                
                # Check License
                licenses = meta.get('license', [])
                if not any(LICENSE_FILTER in lic for lic in licenses if lic):
                    continue

                # Check Keywords
                title = meta.get('title', [''])[0]
                abstract = meta.get('abstract', [''])[0].lower()
                comments = meta.get('comments', [''])[0].lower()
                
                full_text = f"{title.lower()} {comments} {abstract[:500]}"

                if any(kw in full_text for kw in KEYWORDS):
                    matches += 1
                    pid = meta.get('id', ['Unknown'])[0]
                    forenames = meta.get('forenames', [])
                    keynames = meta.get('keyname', [])
                    authors = [f"{fn} {kn}" if fn else kn
                               for fn, kn in zip(forenames, keynames)]
                    auth = ", ".join(authors[:3])
                    
                    print(f"\n[MATCH {matches}] {title}")
                    print(f"   -> {licenses[0]}")

                    link = f'https://arxiv.org/abs/{pid}'
                    esc_title = title.replace('|', '\\|')
                    esc_auth = auth.replace('|', '\\|')
                    f.write(f'| {pid} | {esc_title} | {esc_auth} | [CC-BY-4.0]({licenses[0]}) | [arxiv]({link}) |\n')
                    f.flush()

                if scanned % 100 == 0:
                    print(f"Scanned {scanned} records...", end='\r')

        except KeyboardInterrupt:
            print("\nStopped by user.")
        except Exception as e:
            print(f"\nError mid-stream: {e}")

    elapsed = str(timedelta(seconds=int(time.time() - start_time)))
    print("\n\n--- REPORT ---")
    print(f"Time: {elapsed}")
    print(f"Scanned: {scanned}")
    print(f"Found: {matches}")
    print(f"Saved to: {OUTPUT_FILE}")

if __name__ == "__main__":
    run_harvester()