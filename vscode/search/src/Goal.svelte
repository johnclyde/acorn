<script lang="ts">
  export let searchResponse: SearchResponse;
  export let showLocation: (uri: string, range: Range) => void;

  function callback() {
    if (searchResponse.goalRange !== null) {
      showLocation(searchResponse.uri, searchResponse.goalRange);
    }
  }
</script>

{#if searchResponse.goalName === null}
  <span class="header">There is no goal.</span>
{:else if searchResponse.goalRange === null}
  <span class="header">{searchResponse.goalName}</span>
{:else}
  <span class="header goal-link" on:click={callback}
        >{searchResponse.goalName}</span>
{/if}

<style>
  .goal-link {
    cursor: pointer;
  }

  .goal-link:hover {
    text-decoration: underline;
  }
</style>
